#!/usr/bin/env python3
"""Lean adapter for trust-ledger: the output of lean/Dump.lean in, an adapter dump (docs/FORMAT.md 2.6) out.

  ledger/dump.sh | python3 adapters/lean.py           # as the `extract` command of [adapter.lean]
  python3 adapters/lean.py --from old-lean.json         # convert a stored Dump.lean output

One node per declaration (kind `lean-decl`), with reference = declaration name:

  content    everything Dump.lean reports except stmt_deps, proof_deps, line and module, plus `name`
  deps       stmt_deps and proof_deps (within the dump)
  spec       {name, kind, type, type_term, value, value_term}: the statement, not the proof. By proof
             irrelevance a refactored proof does not change what a theorem claims, so it does not reset
             attestations; a changed statement or definition does.
  spec_deps  stmt_deps: the declarations occurring in the statement (for a definition: type and value)
  status     ok | conditional (assumes) | open (axioms, sorry)
  register   axiom:<A> for each non-standard axiom, sorry:<name>, hyp:<H> for each assumption
  result     true for theorems (a claim's `Name*` expands to these)
  info       {module, line} (not hashed)

The dump also carries the column title, display texts and legend for the status table (not hashed).

The environment (toolchain) is reported once for the whole dump.
"""
import json, sys

VERSION = "0.2.0"
STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
WORDS = ["ok", "assumes", "axioms", "sorry"]  # best to worst, breaks ties between nodes of equal status
DISPLAY = dict(  # how the status table shows it (not hashed)
    title="Lean",
    labels={"ok": "checked", "assumes": "checked, given", "axioms": "extra axioms", "sorry": "contains sorry"},
    legend="checked = accepted by the Lean kernel with the standard axioms only; checked, given [Hk] = in addition "
           "the hypothesis Hk of the Hypotheses table is assumed, not proved; extra axioms = the proof uses an axiom "
           "beyond the standard ones; contains sorry = the proof is unfinished.")


def node(name, d, names):
    if d["kind"] == "theorem" and not d.get("proof_term") and not d.get("proof"):
        sys.exit(f"theorem {name} has no proof term (extractor bug?)")
    sd = sorted({x for x in d.get("stmt_deps", []) if x in names})
    pd = sorted({x for x in d.get("proof_deps", []) if x in names})
    axioms = [a for a in d.get("axioms", []) if a not in STANDARD_AXIOMS and a != "sorryAx"]
    sorry = d.get("sorry") or "sorryAx" in d.get("axioms", [])
    status, word = ("open", "sorry") if sorry else ("open", "axioms") if axioms else \
        ("conditional", "assumes") if d.get("assumptions") else ("ok", "ok")
    register = [f"axiom:{a}" for a in axioms] + ([f"sorry:{name}"] if sorry else []) + \
        [f"hyp:{a}" for a in d.get("assumptions", [])]
    return dict(kind="lean-decl",
                content={k: v for k, v in d.items() if k not in ("stmt_deps", "proof_deps", "line", "module")} | dict(name=name),
                deps=sorted(set(sd) | set(pd)),
                spec={k: d.get(k, "") for k in ("kind", "type", "type_term", "value", "value_term")} | dict(name=name),
                spec_deps=sd, status=status, word=word, register=sorted(register),
                result=d["kind"] == "theorem",
                info={k: d[k] for k in ("module", "line") if k in d})


def convert(dump):
    decls = dump["decls"]
    out = dict(adapter="lean", version=VERSION, environment=dict(toolchain=dump.get("toolchain", "")), words=WORDS,
               **DISPLAY, nodes={n: node(n, d, decls) for n, d in sorted(decls.items())})
    if "env_hash" in dump:  # written by `ledger.py extract`; lets it notice that the sources moved on
        out["env_hash"] = dump["env_hash"]
    return out


def main():
    args = sys.argv[1:]
    src = open(args[1]) if args[:1] == ["--from"] and len(args) == 2 else sys.stdin
    print(json.dumps(convert(json.load(src)), indent=1, sort_keys=True, ensure_ascii=False))


if __name__ == "__main__":
    main()
