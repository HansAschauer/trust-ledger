#!/usr/bin/env python3
"""ProVerif adapter for trust-ledger: references on stdin, adapter dump (docs/FORMAT.md 2.6) on stdout.

A reference is `path/to/model.pv#query text`, the query exactly as written after `query` in the model
(e.g. `attacker(secret)`). Every model named by a reference is run once; the dump has one node per
query of that model:

  kind     proverif-query
  content  {file, sha256, query, result}      result: true | false | cannot be proved
  status   ok (true) | failed (false: an attack was found) | open (cannot be proved)
  register model:<file>   (the model's faithfulness to the protocol is not checked by ProVerif)

ProVerif is called as `$PROVERIF <absolute path of the model>` (default `proverif`). For Docker, mount
the project at the same path, e.g. PROVERIF="docker run --rm -i -v $PWD:$PWD IMAGE proverif".
Query results are matched by position with the `query` lines of the model, because ProVerif reports
queries in a normalised form, not as written.
"""
import hashlib, json, os, re, shlex, subprocess, sys
from pathlib import Path

VERSION = "0.1.0"
WORD = {"true": ("ok", "ok"), "false": ("failed", "false"), "cannot be proved": ("open", "unproved")}
DISPLAY = dict(  # how the status table shows it (not hashed)
    title="ProVerif",
    labels={"ok": "query true", "false": "query false", "unproved": "cannot be proved"},
    legend="query true/false = the named query of the cited model, checked by ProVerif (a false query is an attack "
           "on that model, not a proof of insecurity of the protocol); cannot be proved = inconclusive.")


def queries_of(text):
    """The `query ...` declarations of a model, as written (comments removed)."""
    text = re.sub(r"\(\*.*?\*\)", "", text, flags=re.S)
    return re.findall(r"(?m)^\s*query\s+(.+?)\s*\.\s*$", text)


def results_of(output):
    """'true' | 'false' | 'cannot be proved' for each query, in order, from ProVerif's verification summary."""
    m = re.search(r"Verification summary:\n(.*?)\n-{10,}", output, re.S)
    return re.findall(r"(?m)^Query .+? (?:is|cannot be) (true|false|proved)\.$", m.group(1) if m else "")


def run(path, command):
    proc = subprocess.run(shlex.split(command) + [str(path.resolve())], capture_output=True, text=True)
    results = ["cannot be proved" if r == "proved" else r for r in results_of(proc.stdout)]
    queries = queries_of(path.read_text())
    if len(results) != len(queries):
        sys.stderr.write(proc.stdout[-3000:] + proc.stderr[-3000:])
        sys.exit(f"{path}: {len(queries)} query declarations but {len(results)} results in the ProVerif output")
    return dict(zip(queries, results))


def main():
    command = os.environ.get("PROVERIF", "proverif")
    refs = [l.strip() for l in sys.stdin if l.strip()]
    for r in refs:
        if "#" not in r:
            sys.exit(f"reference {r!r}: expected 'model.pv#query'")
    nodes = {}
    for f in sorted({r.split("#", 1)[0] for r in refs}):
        path = Path(f)
        if not path.is_file():
            sys.exit(f"{f}: no such model")
        sha = hashlib.sha256(path.read_bytes()).hexdigest()
        for q, result in run(path, command).items():
            status, word = WORD[result]
            nodes[f"{f}#{q}"] = dict(kind="proverif-query", content=dict(file=f, sha256=sha, query=q, result=result),
                                     status=status, word=word, register=[f"model:{f}"])
    print(json.dumps(dict(adapter="proverif", version=VERSION, **DISPLAY, nodes=nodes), indent=1, sort_keys=True))


if __name__ == "__main__":
    main()
