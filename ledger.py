#!/usr/bin/env python3
"""trust-ledger: a Merkle ledger of the evidence behind a paper's claims.

Single file, Python >= 3.11, standard library only. Normative format: docs/FORMAT.md.

  ledger.py [-C DIR] status [--strict]   table of claims: Lean status, attestation, register size
  ledger.py [-C DIR] why CLAIM           everything CLAIM rests on, and who attested what
  ledger.py [-C DIR] lock                recompute and write ledger/lock.json (prints the root)
  ledger.py [-C DIR] verify              recompute and compare with lock.json; exit 1 on any difference
  ledger.py [-C DIR] attest CLAIM --person P --level green|yellow|conjecture [--reason R] [--checklist A1,A2]
  ledger.py [-C DIR] extract             run the configured extractor (writes the Lean dump)

DIR is the project root; it must contain ledger/ledger.toml.
"""
import argparse, datetime, hashlib, json, subprocess, sys, tomllib
from pathlib import Path

STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
LEVELS = ("green", "yellow", "conjecture")
EVIDENCE = ("E1", "E2", "E3", "E4", "E5")


# ---------------------------------------------------------------- hashing (FORMAT.md section 2)
def canon(x):
    def check(v):
        if isinstance(v, float):
            raise ValueError("floats are not allowed in hashed content")
        if isinstance(v, dict):
            for k, w in v.items():
                check(k); check(w)
        elif isinstance(v, (list, tuple)):
            for w in v:
                check(w)
    check(x)
    return json.dumps(x, sort_keys=True, separators=(",", ":"), ensure_ascii=False)


def H(tag, x):
    return hashlib.sha256(("trust-ledger/0\0" + tag + "\0" + canon(x)).encode("utf-8")).hexdigest()


def sha_file(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def merkle(payload, deps, tag):
    """Hash every node of a graph. payload: id -> JSON value; deps: id -> list of ids (all ids
    must be keys of payload). Strongly connected components are hashed as one unit."""
    sccs, index, low, onstack, stack, counter = [], {}, {}, set(), [], [0]
    sys.setrecursionlimit(max(10000, 4 * len(payload)))

    def tarjan(v):
        index[v] = low[v] = counter[0]; counter[0] += 1
        stack.append(v); onstack.add(v)
        for w in deps.get(v, ()):
            if w not in index:
                tarjan(w); low[v] = min(low[v], low[w])
            elif w in onstack:
                low[v] = min(low[v], index[w])
        if low[v] == index[v]:
            comp = []
            while True:
                w = stack.pop(); onstack.discard(w); comp.append(w)
                if w == v:
                    break
            sccs.append(sorted(comp))  # Tarjan emits dependencies first

    for v in sorted(payload):
        if v not in index:
            tarjan(v)
    h = {}
    for comp in sccs:
        ext = sorted({d for m in comp for d in deps.get(m, ()) if d not in comp})
        extdeps = [[d, h[d]] for d in ext]
        if len(comp) == 1 and comp[0] not in deps.get(comp[0], ()):
            v = comp[0]
            h[v] = H(tag, {"p": payload[v], "deps": [[d, h[d]] for d in sorted(set(deps.get(v, ())))]})
        else:
            hc = H(tag + "-scc", {"members": [[m, payload[m]] for m in comp], "deps": extdeps})
            for m in comp:
                h[m] = H(tag + "-member", [m, hc])
    return h


# ---------------------------------------------------------------- loading
class Ledger:
    def __init__(self, root):
        self.root = Path(root).resolve()
        self.dir = self.root / "ledger"
        cfgfile = self.dir / "ledger.toml"
        if not cfgfile.exists():
            sys.exit(f"{cfgfile} not found")
        self.cfg = tomllib.loads(cfgfile.read_text())
        self.errors = []
        self.load_human()
        self.load_lean()
        self.build()

    def load_human(self):
        self.claims, self.citations, self.assertions, self.attestations = {}, {}, {}, []
        for f in sorted(self.dir.glob("*.toml")):
            if f.name == "ledger.toml":
                continue
            t = tomllib.loads(f.read_text())
            self.claims.update(t.get("claim", {}))
            self.citations.update(t.get("citation", {}))
            self.assertions.update(t.get("assertion", {}))
            self.attestations += t.get("attestation", [])
        for n, c in self.claims.items():
            if c.get("evidence", "E5") not in EVIDENCE:
                self.errors.append(f"claim {n}: unknown evidence type {c['evidence']!r}")
        for a in self.attestations:
            if a.get("level") not in LEVELS:
                self.errors.append(f"attestation on {a.get('claim')}: unknown level {a.get('level')!r}")
            elif a["level"] == "yellow" and not a.get("reason"):
                self.errors.append(f"attestation on {a.get('claim')}: yellow needs a reason")

    def load_lean(self):
        self.decls, self.toolchain = {}, ""
        lc = self.cfg.get("lean")
        if not lc:
            return
        p = self.dir / lc.get("dump", "lean.json")
        if p.exists():
            d = json.loads(p.read_text())
            self.decls, self.toolchain = d["decls"], d.get("toolchain", "")
        elif any(c.get("lean") for c in self.claims.values()):
            self.errors.append(f"{p} missing: run `ledger.py extract`")

    # -------------------------------------------------------- graph
    def build(self):
        payload, deps = {}, {}  # full graph
        env_files = {f: sha_file(self.root / f) for f in self.cfg.get("environment", {}).get("files", [])
                     if (self.root / f).exists()}
        env = "env:" + self.cfg.get("project", {}).get("name", "project")
        payload[env] = dict(kind="environment", provenance="computed",
                            content=dict(toolchain=self.toolchain, files=env_files))
        deps[env] = []
        self.spec_payload, self.spec_deps = {}, {}
        for n, d in self.decls.items():
            i = "lean:" + n
            if d["kind"] == "theorem" and not d.get("proof_term") and not d.get("proof"):
                self.errors.append(f"dump: theorem {n} has no proof term (extractor bug?)")
            payload[i] = dict(kind="lean-decl", provenance="computed", content=dict(
                {k: v for k, v in d.items() if k not in ("stmt_deps", "proof_deps", "line", "module")}, name=n))
            sd = sorted({"lean:" + x for x in d.get("stmt_deps", []) if x in self.decls})
            pd = sorted({"lean:" + x for x in d.get("proof_deps", []) if x in self.decls})
            deps[i] = sorted(set(sd) | set(pd) | {env})
            self.spec_payload[i] = {k: d.get(k, "") for k in ("kind", "type", "type_term", "value", "value_term")} | dict(name=n)
            self.spec_deps[i] = sd
        for n, c in self.citations.items():
            i = "cite:" + n
            payload[i] = dict(kind="citation", provenance="asserted",
                              content=dict(key=c.get("key", n), statement=c.get("statement", ""), source=c.get("source", "")))
            deps[i] = []
        for n, a in self.assertions.items():
            i = "assert:" + n
            payload[i] = dict(kind="assertion", provenance="asserted", content=dict(claim=a["claim"], text=a["text"]))
            deps[i] = []
        self.files = {}
        for n, c in self.claims.items():
            for f in c.get("files", []):
                i = "file:" + f
                if i in payload:
                    continue
                if not (self.root / f).exists():
                    self.errors.append(f"claim {n}: file {f} not found")
                    continue
                payload[i] = dict(kind="file", provenance="computed", content=dict(path=f, sha256=sha_file(self.root / f)))
                deps[i] = []
        for n, c in self.claims.items():
            i = "claim:" + n
            d = []
            for x in c.get("lean", []):
                if x in self.decls:
                    d.append("lean:" + x)
                else:
                    self.errors.append(f"claim {n}: Lean declaration {x} not in dump")
            d += ["file:" + f for f in c.get("files", []) if "file:" + f in payload]
            for x in c.get("cites", []):
                if x in self.citations:
                    d.append("cite:" + x)
                else:
                    self.errors.append(f"claim {n}: unknown citation {x}")
            d += ["assert:" + a for a, v in self.assertions.items() if v["claim"] == n]
            for u in c.get("uses", []):
                if u in self.claims:
                    d.append("claim:" + u)
                else:
                    self.errors.append(f"claim {n}: unknown claim {u} in uses")
            payload[i] = dict(kind="claim", provenance="asserted", content=dict(
                text=c.get("text", ""), label=c.get("label", ""), evidence=c.get("evidence", "E5")))
            deps[i] = sorted(set(d))
        self.attest_ids = []
        for k, a in enumerate(self.attestations):
            i = f"attest:{k}"
            if "claim:" + a.get("claim", "") not in payload:
                self.errors.append(f"attestation {k}: unknown claim {a.get('claim')}")
                continue
            payload[i] = dict(kind="attestation", provenance="asserted", content={
                x: a.get(x, "") for x in ("claim", "person", "date", "level", "reason", "bound")} | dict(checklist=a.get("checklist", [])))
            deps[i] = ["claim:" + a["claim"]]
            self.attest_ids.append(i)
        self.full = merkle(payload, deps, "node")
        self.payload, self.deps, self.env = payload, deps, env
        # spec hashes of declarations, then of claims
        self.spec = merkle(self.spec_payload, self.spec_deps, "spec")
        cp, cd = {}, {}
        for n, c in self.claims.items():
            cp[n] = dict(text=c.get("text", ""),
                         lean=[[x, self.spec.get("lean:" + x, "")] for x in sorted(c.get("lean", []))],
                         others=[[i, self.full[i]] for i in sorted(deps["claim:" + n]) if not i.startswith(("lean:", "claim:"))])
            cd[n] = [u for u in c.get("uses", []) if u in self.claims]
        self.cspec = merkle(cp, cd, "claim-spec")
        self.root_hash = H("root", [[i, self.full[i]] for i in sorted(payload)
                                    if payload[i]["kind"] in ("claim", "attestation", "environment")])
        self.register = self.compute_register()

    def compute_register(self):
        own = {}
        for n, c in self.claims.items():
            r = set()
            for x in c.get("lean", []):
                d = self.decls.get(x)
                if not d:
                    continue
                r |= {"axiom:" + a for a in d.get("axioms", []) if a not in STANDARD_AXIOMS and a != "sorryAx"}
                if d.get("sorry") or "sorryAx" in d.get("axioms", []):
                    r.add("sorry:" + x)
                r |= {"hyp:" + a for a in d.get("assumptions", [])}
            r |= {"hyp:cited:" + x for x in c.get("cites", [])}
            r |= {"assertion:" + a for a, v in self.assertions.items() if v["claim"] == n}
            if not c.get("lean") and not c.get("files"):
                r.add("evidence:none")
            own[n] = r
        reg = {n: set(r) for n, r in own.items()}
        changed = True
        while changed:  # least fixed point; terminates since sets only grow
            changed = False
            for n, c in self.claims.items():
                for u in c.get("uses", []):
                    if u in reg and not reg[u] <= reg[n]:
                        reg[n] |= reg[u]; changed = True
        return {n: sorted(r) for n, r in reg.items()}

    # -------------------------------------------------------- derived views
    def lean_status(self, n):
        c = self.claims[n]
        if not c.get("lean"):
            return "-"
        ds = [self.decls.get(x) for x in c["lean"]]
        if any(d is None for d in ds):
            return "missing"
        if any(d.get("sorry") for d in ds):
            return "sorry"
        if any(set(d.get("axioms", [])) - STANDARD_AXIOMS for d in ds):
            return "axioms"
        if any(d.get("assumptions") for d in ds):
            return "assumes"
        return "ok"

    def attestation_state(self, n):
        """Latest attestation per person on claim n -> list of (person, level, date, current?)."""
        latest = {}
        for a in self.attestations:
            if a.get("claim") == n:
                latest[a.get("person", "?")] = a
        cur = self.cspec.get(n)
        return [(p, a.get("level"), a.get("date", ""), a.get("bound") == cur) for p, a in sorted(latest.items())]

    def lock(self):
        return dict(format=0, root=self.root_hash, toolchain=self.toolchain,
                    nodes={i: dict(kind=p["kind"], full=self.full[i]) for i, p in sorted(self.payload.items())},
                    claims={n: dict(spec=self.cspec[n], register=self.register[n]) for n in sorted(self.claims)})


# ---------------------------------------------------------------- commands
def cmd_status(L, args):
    word = {"green": "GREEN", "yellow": "YELLOW", "conjecture": "CONJECTURE"}
    rows = [("claim", "evid", "lean", "attestation", "register")]
    stale = 0
    for n in sorted(L.claims):
        att = []
        for p, lvl, date, cur in L.attestation_state(n):
            att.append(f"{word.get(lvl, lvl)} {p} {'current' if cur else 'STALE'}")
            stale += not cur
        rows.append((n, L.claims[n].get("evidence", "E5"), L.lean_status(n), "; ".join(att) or "none", str(len(L.register[n]))))
    w = [max(len(r[i]) for r in rows) for i in range(5)]
    for r in rows:
        print("  ".join(c.ljust(w[i]) for i, c in enumerate(r)).rstrip())
    print(f"\nroot {L.root_hash}")
    for e in L.errors:
        print("error:", e, file=sys.stderr)
    return 1 if L.errors or (args.strict and stale) else 0


def cmd_why(L, args):
    n = args.claim
    if n not in L.claims:
        sys.exit(f"unknown claim {n}")
    c = L.claims[n]
    print(f"{n}: {c.get('text', '')}\n  evidence {c.get('evidence', 'E5')}, lean {L.lean_status(n)}, spec {L.cspec[n][:12]}")
    print("  rests on:")
    seen, todo = set(), list(L.deps["claim:" + n])
    while todo:
        i = todo.pop()
        if i in seen or i == L.env:
            continue
        seen.add(i)
        todo += L.deps.get(i, [])
    for i in sorted(seen):
        print(f"    {L.payload[i]['provenance']:9} {i}")
    print("  register:", ", ".join(L.register[n]) or "(empty)")
    for p, lvl, date, cur in L.attestation_state(n):
        print(f"  attested {lvl} by {p} on {date}: {'current' if cur else 'STALE (statement changed since)'}")
    return 0


def cmd_lock(L, args):
    if L.errors:
        for e in L.errors:
            print("error:", e, file=sys.stderr)
        return 1
    (L.dir / "lock.json").write_text(json.dumps(L.lock(), indent=1, sort_keys=True) + "\n")
    print(L.root_hash)
    return 0


def cmd_verify(L, args):
    f = L.dir / "lock.json"
    if not f.exists():
        sys.exit("no lock.json: run `lock` first")
    old, new, bad = json.loads(f.read_text()), L.lock(), list(L.errors)
    for i in sorted(set(old["nodes"]) | set(new["nodes"])):
        a, b = old["nodes"].get(i), new["nodes"].get(i)
        if a is None:
            bad.append(f"new node {i}")
        elif b is None:
            bad.append(f"node removed: {i}")
        elif a["full"] != b["full"]:
            bad.append(f"changed: {i}")
    for n in sorted(set(old["claims"]) & set(new["claims"])):
        if old["claims"][n]["register"] != new["claims"][n]["register"]:
            bad.append(f"register of claim {n} differs")
    if old["root"] != new["root"] and not bad:
        bad.append("root differs")
    for b in bad:
        print(b)
    print("OK" if not bad else "FAILED", "root", new["root"])
    return 1 if bad else 0


def cmd_attest(L, args):
    if args.claim not in L.claims:
        sys.exit(f"unknown claim {args.claim}")
    if args.level == "yellow" and not args.reason:
        sys.exit("yellow needs --reason")
    rec = dict(claim=args.claim, person=args.person, date=datetime.date.today().isoformat(), level=args.level,
               reason=args.reason or "", checklist=[x for x in (args.checklist or "").split(",") if x],
               bound=L.cspec[args.claim])
    with open(L.dir / "attestations.toml", "a") as f:
        f.write("\n[[attestation]]\n" + "".join(f"{k} = {json.dumps(v, ensure_ascii=False)}\n" for k, v in rec.items()))
    print(f"recorded {args.level} by {args.person} on {args.claim}, bound to {rec['bound'][:12]}")
    return 0


def cmd_extract(L, args):
    cmd = L.cfg.get("lean", {}).get("extract")
    if not cmd:
        sys.exit("no [lean] extract command configured")
    names = sorted({x for c in L.claims.values() for x in c.get("lean", [])})
    out = subprocess.run(cmd, shell=True, cwd=L.root, input="\n".join(names), text=True, capture_output=True)
    sys.stderr.write(out.stderr[-3000:])
    if out.returncode:
        return out.returncode
    json.loads(out.stdout)  # must be valid JSON
    (L.dir / L.cfg["lean"].get("dump", "lean.json")).write_text(out.stdout)
    return 0


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("-C", dest="dir", default=".")
    sub = ap.add_subparsers(dest="cmd", required=True)
    p = sub.add_parser("status"); p.add_argument("--strict", action="store_true")
    sub.add_parser("lock"); sub.add_parser("verify"); sub.add_parser("extract")
    p = sub.add_parser("why"); p.add_argument("claim")
    p = sub.add_parser("attest"); p.add_argument("claim"); p.add_argument("--person", required=True)
    p.add_argument("--level", required=True, choices=LEVELS); p.add_argument("--reason"); p.add_argument("--checklist")
    args = ap.parse_args(argv)
    if args.cmd == "extract":  # the dump may not exist yet
        L = Ledger.__new__(Ledger)
        L.root = Path(args.dir).resolve(); L.dir = L.root / "ledger"
        L.cfg = tomllib.loads((L.dir / "ledger.toml").read_text()); L.errors = []
        L.load_human()
    else:
        L = Ledger(args.dir)
    return globals()["cmd_" + args.cmd](L, args)


if __name__ == "__main__":
    sys.exit(main())
