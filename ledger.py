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
import argparse, datetime, hashlib, json, re, subprocess, sys, tomllib
from pathlib import Path

STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
LEVELS = ("green", "yellow", "conjecture")
ROOT_KINDS = ("claim", "attestation", "environment", "paper-source")
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


# ---------------------------------------------------------------- LaTeX: sources and statements
STATEMENT_ENVS = {"theorem", "proposition", "lemma", "corollary", "definition", "example", "remark",
                  "conjecture", "claim", "fact", "observation", "assumption", "problem"}
MATH_ENVS = {"equation", "align", "gather", "multline", "eqnarray", "flalign", "alignat"}
INPUT_RE = re.compile(r"\\(?:input|include)\s*\{([^}]+)\}")
BIB_RE = re.compile(r"\\bibliography\s*\{([^}]+)\}")
ENV_RE = re.compile(r"\\(begin|end)\{([A-Za-z]+\*?)\}")


def strip_comments(text):
    """Remove TeX comments: a % that is not preceded by an odd number of backslashes."""
    out = []
    for line in text.split("\n"):
        i = 0
        while i < len(line):
            if line[i] == "\\":
                i += 2
                continue
            if line[i] == "%":
                line = line[:i]
                break
            i += 1
        out.append(line)
    return "\n".join(out)


def tex_sources(main, search, excluded):
    """The .tex files reached from `main` by \\input/\\include (in order) and the .bib files named by
    \\bibliography; files below an excluded directory are left out. Returns (paths, unresolved names)."""
    def resolve(name, cur, exts):  # like TeX: relative to the directory LaTeX runs in, not to `cur`
        for base in [Path(main).resolve().parent, *search]:
            for e in exts:
                cand = base / (name if (e == "" or name.endswith(e)) else name + e)
                if cand.is_file():
                    return cand.resolve()
        return None

    def is_excluded(path):
        return any(path == x or x in path.parents for x in excluded)

    files, unresolved, todo = [], [], [Path(main).resolve()]
    while todo:
        cur = todo.pop(0)
        if cur in files or is_excluded(cur):
            continue
        files.append(cur)
        if cur.suffix != ".tex":
            continue
        text = strip_comments(cur.read_text(errors="replace"))
        for m in INPUT_RE.finditer(text):
            r = resolve(m.group(1).strip(), cur, ("", ".tex"))
            if r is None:
                unresolved.append(m.group(1).strip())
            else:
                todo.append(r)
        for m in BIB_RE.finditer(text):
            for name in m.group(1).split(","):
                r = resolve(name.strip(), cur, (".bib",))
                if r is None:
                    unresolved.append(name.strip() + ".bib")
                else:
                    todo.append(r)
    return files, sorted(set(unresolved))


def find_environments(text):
    """Statement and display-math environments of `text`: (name, body_start, body_end)."""
    stack, envs = [], []
    for m in ENV_RE.finditer(text):
        kind, name = m.group(1), m.group(2)
        base = name.rstrip("*")
        if base not in STATEMENT_ENVS and base not in MATH_ENVS:
            continue
        if kind == "begin":
            stack.append((name, m.end()))
        else:
            for k in range(len(stack) - 1, -1, -1):
                if stack[k][0] == name:
                    envs.append((name, stack[k][1], m.start()))
                    del stack[k:]
                    break
    return envs


def statement_of(label, parsed):
    """Text of the innermost statement/math environment containing \\label{label}, whitespace
    normalised, comments and labels removed. parsed: [(text, envs)]. Returns (text|None, problem|None)."""
    pat = re.compile(r"\\label\{" + re.escape(label) + r"\}")
    for text, envs in parsed:
        m = pat.search(text)
        if not m:
            continue
        best = None
        for e in envs:
            if e[1] <= m.start() < e[2] and (best is None or e[1] > best[1]):
                best = e
        if best is None:
            return None, f"label {label} is not inside a theorem-like or display-math environment"
        body = re.sub(r"\\label\{[^}]*\}", "", text[best[1]:best[2]])
        return f"{best[0]}: " + " ".join(body.split()), None
    return None, f"label {label} not found in the paper source"


# ---------------------------------------------------------------- loading
class Ledger:
    def __init__(self, root, paper=None):
        self.root = Path(root).resolve()
        self.dir = self.root / "ledger"
        cfgfile = self.dir / "ledger.toml"
        if not cfgfile.exists():
            sys.exit(f"{cfgfile} not found")
        self.cfg = tomllib.loads(cfgfile.read_text())
        self.paper = paper
        self.errors = []
        self.load_human()
        self.load_lean()
        self.load_papers()
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
        self.apply_scope()
        for a in self.attestations:
            if a.get("level") not in LEVELS:
                self.errors.append(f"attestation on {a.get('claim')}: unknown level {a.get('level')!r}")
            elif a["level"] == "yellow" and not a.get("reason"):
                self.errors.append(f"attestation on {a.get('claim')}: yellow needs a reason")

    @property
    def lockfile(self):
        return self.dir / ("lock.json" if self.paper is None else f"lock-{self.paper}.json")

    def apply_scope(self):
        """With a paper selected keep its claims (and those without a paper), plus every claim they use."""
        papers = self.cfg.get("paper", {})
        if self.paper is None:
            return
        if papers and self.paper not in papers:
            self.errors.append(f"unknown paper {self.paper!r}; configured: {', '.join(sorted(papers))}")
        keep = {n for n, c in self.claims.items() if c.get("paper") in (None, self.paper)}
        todo = list(keep)
        while todo:
            for u in self.claims[todo.pop()].get("uses", []):
                if u in self.claims and u not in keep:
                    keep.add(u); todo.append(u)
        self.claims = {n: c for n, c in self.claims.items() if n in keep}
        self.attestations = [a for a in self.attestations if a.get("claim") in keep]
        self.assertions = {k: v for k, v in self.assertions.items() if v.get("claim") in keep}
        used = {x for c in self.claims.values() for x in c.get("cites", [])}
        self.citations = {k: v for k, v in self.citations.items() if k in used}

    def load_papers(self):
        """Paper-source nodes and the parsed statement environments of each paper."""
        self.paper_nodes, self.parsed, self.unresolved = {}, {}, {}
        papers = self.cfg.get("paper", {})
        excluded = [(self.root / d).resolve() for d in self.cfg.get("generated", {}).get("dirs", [])]
        for name, pc in papers.items():
            if self.paper is not None and name != self.paper:
                continue
            main = self.root / pc["main"]
            if not main.is_file():
                self.errors.append(f"paper {name}: {main} not found")
                continue
            search = [(self.root / d).resolve() for d in pc.get("texinputs", [])]
            files, unresolved = tex_sources(main, search, excluded)
            self.unresolved[name] = unresolved
            rel = lambda f: str(f.relative_to(self.root)) if self.root in f.parents else str(f)
            self.paper_nodes[name] = dict(main=pc["main"], files={rel(f): sha_file(f) for f in files},
                                          unresolved=unresolved)
            self.parsed[name] = [(t, find_environments(t)) for t in
                                 (strip_comments(f.read_text(errors="replace")) for f in files if f.suffix == ".tex")]

    def label_position(self, c):
        """(file index, offset) of the claim's first label in its paper, for ordering; None if absent."""
        labels = c.get("labels") or ([c["label"]] if c.get("label") else [])
        for lab in labels:
            for k, (text, _) in enumerate(self.parsed.get(c.get("paper"), [])):
                m = re.search(r"\\label\{" + re.escape(lab) + r"\}", text)
                if m:
                    return (k, m.start())
        return None

    def attestation_summary(self, n):
        """'green'|'yellow'|'conjecture' (strongest current), 'stale' (only stale ones) or 'none'."""
        st = self.attestation_state(n)
        cur = [lvl for _, lvl, _, ok in st if ok]
        for lvl in LEVELS:
            if lvl in cur:
                return lvl
        return "stale" if st else "none"

    def statement(self, n, c):
        """(text, source): the claim's statement from the paper's LaTeX if it has labels, else its `text`."""
        labels = c.get("labels") or ([c["label"]] if c.get("label") else [])
        sources = self.parsed.get(c.get("paper")) if c.get("paper") in self.parsed else \
            [x for v in self.parsed.values() for x in v]
        if not labels or not sources:
            return c.get("text", ""), "manual"
        parts = []
        for lab in labels:
            t, problem = statement_of(lab, sources)
            if problem:
                self.errors.append(f"claim {n}: {problem}")
            else:
                parts.append(f"[{lab}] {t}")
        return "\n".join(parts), "tex"

    def env_files(self):
        """Files of the environment node: paths or globs (relative to the project root), sorted."""
        excluded = [(self.root / d).resolve() for d in self.cfg.get("generated", {}).get("dirs", [])]
        out = set()
        for pat in self.cfg.get("environment", {}).get("files", []):
            for f in self.root.glob(pat):
                r = f.resolve()
                if f.is_file() and not any(x == r or x in r.parents for x in excluded):  # generated files depend on the root
                    out.add(str(f.relative_to(self.root)))
        return sorted(out)

    def env_hash(self):
        return H("env-files", {f: sha_file(self.root / f) for f in self.env_files()})

    def load_lean(self):
        self.decls, self.toolchain = {}, ""
        lc = self.cfg.get("lean")
        if not lc:
            return
        p = self.dir / lc.get("dump", "lean.json")
        if p.exists():
            d = json.loads(p.read_text())
            self.decls, self.toolchain = d["decls"], d.get("toolchain", "")
            if d.get("env_hash") and d["env_hash"] != self.env_hash():
                self.errors.append(f"{p.name} is older than the sources it was extracted from "
                                   "(environment files changed): run `ledger.py extract`")
        elif any(c.get("lean") for c in self.claims.values()):
            self.errors.append(f"{p} missing: run `ledger.py extract`")

    def expand_lean(self, names):
        out = []
        for x in names:
            if x.endswith("*"):
                out += sorted(n for n, d in self.decls.items() if n.startswith(x[:-1]) and d["kind"] == "theorem")
            else:
                out.append(x)
        return out

    # -------------------------------------------------------- graph
    def build(self):
        payload, deps = {}, {}  # full graph
        env_files = {f: sha_file(self.root / f) for f in self.env_files()}
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
        for name, pn in self.paper_nodes.items():
            payload["paper:" + name] = dict(kind="paper-source", provenance="computed", content=pn)
            deps["paper:" + name] = []
        self.stmt = {}
        for n, c in self.claims.items():
            c["lean"] = self.expand_lean(c.get("lean", []))
            self.stmt[n] = self.statement(n, c)
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
                text=self.stmt[n][0], source=self.stmt[n][1], label=c.get("label", ""), evidence=c.get("evidence", "E5")))
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
        seen, todo = set(), [i for i, q in payload.items() if q["kind"] in ROOT_KINDS]
        while todo:  # keep only what the roots rest on (matters when a paper is selected)
            i = todo.pop()
            if i not in seen:
                seen.add(i); todo += deps.get(i, [])
        payload = {i: q for i, q in payload.items() if i in seen}
        self.full = {i: h for i, h in self.full.items() if i in seen}
        self.payload, self.deps, self.env = payload, deps, env
        # spec hashes of declarations, then of claims
        self.spec = merkle(self.spec_payload, self.spec_deps, "spec")
        cp, cd = {}, {}
        for n, c in self.claims.items():
            cp[n] = dict(text=self.stmt[n][0],
                         lean=[[x, self.spec.get("lean:" + x, "")] for x in sorted(c.get("lean", []))],
                         others=[[i, self.full[i]] for i in sorted(deps["claim:" + n]) if not i.startswith(("lean:", "claim:"))])
            cd[n] = [u for u in c.get("uses", []) if u in self.claims]
        self.cspec = merkle(cp, cd, "claim-spec")
        self.root_hash = H("root", [[i, self.full[i]] for i in sorted(payload)
                                    if payload[i]["kind"] in ROOT_KINDS])
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
    rows = [("claim", "evid", "stmt", "lean", "attestation", "register")]
    stale = 0
    for n in sorted(L.claims):
        att = []
        for p, lvl, date, cur in L.attestation_state(n):
            att.append(f"{word.get(lvl, lvl)} {p} {'current' if cur else 'STALE'}")
            stale += not cur
        rows.append((n, L.claims[n].get("evidence", "E5"), L.stmt[n][1], L.lean_status(n), "; ".join(att) or "none",
                     str(len(L.register[n]))))
    w = [max(len(r[i]) for r in rows) for i in range(6)]
    for r in rows:
        print("  ".join(c.ljust(w[i]) for i, c in enumerate(r)).rstrip())
    print(f"\nroot {L.root_hash}" + (f"  (paper {L.paper})" if L.paper else ""))
    for name, u in L.unresolved.items():
        if u:
            print(f"warning: paper {name}: could not resolve {', '.join(u)}", file=sys.stderr)
    for e in L.errors:
        print("error:", e, file=sys.stderr)
    return 1 if L.errors or (args.strict and stale) else 0


def cmd_why(L, args):
    n = args.claim
    if n not in L.claims:
        sys.exit(f"unknown claim {n}")
    c = L.claims[n]
    print(f"{n} [{L.stmt[n][1]}]: {L.stmt[n][0]}\n  evidence {c.get('evidence', 'E5')}, lean {L.lean_status(n)}, spec {L.cspec[n][:12]}")
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


TEX_SPECIAL = {"\\": r"\textbackslash{}", "&": r"\&", "%": r"\%", "$": r"\$", "#": r"\#", "_": r"\_",
               "{": r"\{", "}": r"\}", "~": r"\textasciitilde{}", "^": r"\textasciicircum{}"}


def tex_esc(x):
    return "".join(TEX_SPECIAL.get(ch, ch) for ch in str(x))


def cmd_tex(L, args):
    """Write the generated files the paper's \\usepackage{ledgercheck} reads."""
    if not L.paper:
        sys.exit("tex needs a paper: ledger.py -P PAPER tex")
    gen = L.cfg.get("generated", {}).get("dirs", [])
    if not gen:
        sys.exit("ledger.toml: [generated] dirs must name the directory for generated files")
    if L.errors:
        for e in L.errors:
            print("error:", e, file=sys.stderr)
        return 1
    out = L.root / gen[0]
    out.mkdir(parents=True, exist_ok=True)
    pc = L.cfg.get("paper", {}).get(L.paper, {})
    src = L.full.get("paper:" + L.paper, "")[:12]
    tool = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()[:12]
    r = L.root_hash
    lines = [f"% generated by ledger.py -P {L.paper} tex; do not edit. Excluded from the hashed source.",
             f"\\def\\LedgerPaper{{{L.paper}}}", f"\\def\\LedgerRoot{{{r}}}", f"\\def\\LedgerRootShort{{{r[:12]}}}"]
    lines += [f"\\def\\LedgerRoot{c}{{{r[16 * k:16 * k + 16]}}}" for k, c in enumerate("ABCD")]
    lines += [f"\\def\\LedgerSource{{{src}}}", f"\\def\\LedgerTool{{{tool}}}",
              f"\\def\\LedgerFormat{{0}}", f"\\def\\LedgerDate{{{datetime.date.today().isoformat()}}}",
              "\\def\\LedgerSupplement{%s}" % tex_esc(pc.get("supplement", "the supplementary repository of this paper")),
              "\\def\\LedgerVerify{%s}" % tex_esc(pc.get("verify", f"python3 ledger.py -P {L.paper} verify"))]
    (out / f"ledger-{L.paper}-root.tex").write_text("\n".join(lines) + "\n")

    # one row per label (readers look up "Theorem X"); a claim without labels gets one row under its name
    def label_pos(c, lab):
        for k, (text, _) in enumerate(L.parsed.get(c.get("paper"), [])):
            m = re.search(r"\\label\{" + re.escape(lab) + r"\}", text)
            if m:
                return (0, k, m.start())
        return (1, 0, 0)
    entries = []
    for n, c in L.claims.items():
        labels = c.get("labels") or ([c["label"]] if c.get("label") else [])
        entries += [(label_pos(c, lab), lab, n) for lab in labels] or [((2, 0, 0), n, n)]
    entries.sort()
    names = sorted(L.claims)
    cnt = dict(green=0, yellow=0, conjecture=0, stale=0, none=0)
    assumes = sorry = 0
    for n in names:
        cnt[L.attestation_summary(n)] += 1
        ls = L.lean_status(n)
        assumes += ls == "assumes"; sorry += ls == "sorry"
    rows = []
    seen = {}
    for _, lab, n in entries:
        seen[lab] = seen.get(lab, 0) + 1
    for _, lab, n in entries:
        c = L.claims[n]
        ls = L.lean_status(n)
        st = L.attestation_state(n)
        att = "; ".join(
            f"\\LedgerAtt{{{lvl}}}{{{tex_esc(p)}}}{{{tex_esc(date)}}}{{{'current' if cur else 'stale'}}}" for p, lvl, date, cur in st
        ) or "\\LedgerNoAtt"
        res = f"\\texttt{{{tex_esc(lab)}}}" + (f" {{\\scriptsize({tex_esc(n)})}}" if seen[lab] > 1 and lab != n else "")
        rows.append(f"\\LedgerRow{{{res}}}{{{c.get('evidence', 'E5')}}}{{{L.stmt[n][1]}}}"
                    f"{{\\LedgerLeanCell{{{ls if ls != '-' else 'none'}}}}}{{{len(L.register[n])}}}{{{att}}}")
    cl = [f"% generated by ledger.py -P {L.paper} tex; do not edit. Excluded from the hashed source.",
          f"\\def\\LedgerNClaims{{{len(names)}}}"]
    cl += [f"\\def\\LedgerN{k}{{{v}}}" for k, v in (("Green", cnt["green"]), ("Yellow", cnt["yellow"]),
           ("Conj", cnt["conjecture"]), ("Stale", cnt["stale"]), ("None", cnt["none"]), ("Assumes", assumes), ("Sorry", sorry))]
    # plain tabulars of CHUNK rows each: page breaks fall between them (longtable/supertabular fail in
    # the two-column journal class)
    CHUNK = 8
    cl += ["\\def\\LedgerChunks{%"]
    for k in range(0, len(rows), CHUNK):
        cl += ["\\LedgerTable{%"] + [r + "%" for r in rows[k:k + CHUNK]] + ["}%"]
    cl += ["}"]
    (out / f"ledger-{L.paper}-status.tex").write_text("\n".join(cl) + "\n")
    print(f"wrote {out / f'ledger-{L.paper}-root.tex'} and {out / f'ledger-{L.paper}-status.tex'}")
    print(r)
    return 0


def cmd_lock(L, args):
    if L.errors:
        for e in L.errors:
            print("error:", e, file=sys.stderr)
        return 1
    L.lockfile.write_text(json.dumps(L.lock(), indent=1, sort_keys=True) + "\n")
    print(L.root_hash)
    return 0


def cmd_verify(L, args):
    f = L.lockfile
    if not f.exists():
        sys.exit(f"no {f.name}: run `lock` first")
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
    dump = json.loads(out.stdout)  # must be valid JSON
    L.root = Path(args.dir).resolve()
    dump["env_hash"] = L.env_hash()  # lets later runs notice that the sources moved on
    (L.dir / L.cfg["lean"].get("dump", "lean.json")).write_text(json.dumps(dump, separators=(",", ":")))
    return 0


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("-C", dest="dir", default=".")
    ap.add_argument("-P", "--paper", default=None, help="restrict to the claims of one configured paper (own root and lock file)")
    sub = ap.add_subparsers(dest="cmd", required=True)
    p = sub.add_parser("status"); p.add_argument("--strict", action="store_true")
    sub.add_parser("lock"); sub.add_parser("verify"); sub.add_parser("extract"); sub.add_parser("tex")
    p = sub.add_parser("why"); p.add_argument("claim")
    p = sub.add_parser("attest"); p.add_argument("claim"); p.add_argument("--person", required=True)
    p.add_argument("--level", required=True, choices=LEVELS); p.add_argument("--reason"); p.add_argument("--checklist")
    args = ap.parse_args(argv)
    if args.cmd == "extract":  # the dump may not exist yet
        L = Ledger.__new__(Ledger)
        L.root = Path(args.dir).resolve(); L.dir = L.root / "ledger"
        L.cfg = tomllib.loads((L.dir / "ledger.toml").read_text()); L.errors = []; L.paper = args.paper
        L.load_human()
    else:
        L = Ledger(args.dir, args.paper)
    return globals()["cmd_" + args.cmd](L, args)


if __name__ == "__main__":
    sys.exit(main())
