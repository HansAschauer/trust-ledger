# AGENTS.md: trust-ledger

Notes for coding agents working in this repository. Human-facing documentation is `README.md`; the normative spec is
`docs/FORMAT.md`.

## What this is

A tamper-evident record of what each result in a paper rests on. Every item (Lean declarations, ProVerif results,
data files, scripts, cited results, assertions, model-generated aids, attestations by named people) becomes a node in a
Merkle DAG with one SHA-256 root per paper. The root is printed in the paper (`tex/ledgercheck.sty`) and recomputed by
`ledger.py verify`. Attestations bind to a claim's *spec* hash, so they go *stale* when the statement or anything it
uses changes. Generated content (back-translations, model assessments) is part of the root but never of a statement
hash and never counts as an attestation.

Status: alpha, tool version 0.3.0, ledger format 0.3.0 (`__version__` / `FORMAT_VERSION` at the top of `ledger.py`).

## Layout

- `ledger.py`: the whole tool, CLI and library, one file (about 3500 lines). Subcommands are `cmd_*` functions; the
  argparse setup is at the end of the file.
- `docs/FORMAT.md`: normative format (canonical JSON, hashing, node kinds, register, adapter dump in 2.6, migration
  in 6). Another implementation must reproduce the same hashes.
- `docs/ARCHITECTURE.md`: fixed core vs. per-field adapters; how to write an adapter. `docs/ROADMAP.md`: agreed
  order and parked ideas.
- `adapters/`: external programs that turn a tool's output into the generic adapter dump (stdin: references, stdout:
  JSON): `lean.py` (behind `lean/Dump.lean`), `proverif.py`, `dvc_steps.py` (needs PyYAML).
- `lean/Dump.lean`: exports theorems/definitions, kernel terms and axioms of a Lake project (run with Lean v4.34.1).
- `tex/ledgercheck.sty`: root, status appendix and `\ledgersummary` in the paper.
- `examples/`: `egg` (the full showcase, with committed attestations, keys, lock and PDF), `toy` (test fixture, Lean +
  ProVerif), `lab` (measurement, manual step, commitment), `prereg` (preregistered study, custom evidence types).
- `tests/test_ledger.py`: unittest suite; works on scratch copies of the examples.

## Hard rules

- **Standard library only, Python 3.11+**, in `ledger.py`. No dependencies. (`tomllib` is why 3.11 is the floor.)
- **Hashes are a contract.** Any change to what enters a `full` or `spec` hash changes roots of existing ledgers.
  That needs a `FORMAT_VERSION` bump, an update to `docs/FORMAT.md`, and a `migrate` path for attestations. Prefer
  additive changes that leave existing hashes unchanged, and check with the committed `examples/egg/ledger/lock-egg.json`.
- The core never runs field-specific tools in `status`, `lock` or `verify`; those read dumps and files only. Tool
  runs belong to `extract`, `check`, `reproduce`, `review`.
- Adapters never hash anything the core recomputes. New field support goes into an adapter or `ledger.toml`
  configuration; if an example needs a core change, the abstraction is wrong (ARCHITECTURE.md, "Test for the design").
- Snapshots (`ledger/snapshots/`), git hints (`git_head`, `git_dirty`) and assessment bindings are hints: not hashed,
  not part of the root. Keep it that way.
- **Library API is used by `trust-ledger-ui`** (sibling repo): `Ledger(root, paper)`, `status_data()` (= `status
  --json`), `claim_detail`, `make_attestation`, `sign_attestation`, `append_attestation`, `diff_since`,
  `record_snapshots`, `LedgerError`, `LEVELS`, `FORMAT_VERSION`, `__version__`. Do not rename or change these
  signatures without updating the UI (`trust-ledger-ui/src/trust_ledger_ui/core/ledgerio.py`).
- `sign_attestation` must keep working with a `*.pub` file and ssh-agent, never prompting for a passphrase.
- Never add attestations, keys or signatures on a person's behalf in a real project. In the examples, the people and
  keys are fictitious and committed on purpose (`examples/egg/private/keys/`).

## Commands

```bash
python3 -m unittest discover -s tests           # all tests; LaTeX tests skip without latexmk/pdflatex/pdftotext
python3 ledger.py -C examples/toy status
python3 ledger.py -C examples/lab reproduce
cd examples/egg && python3 ../../ledger.py -P egg verify   # committed lock must verify
make -C examples/egg                            # extract, check, lock, tex, PDF (needs Lean for extract)
```

CI (`.github/workflows/ci.yml`) runs the tests on Python 3.11 to 3.14 (Linux, macOS), the example commands above, and
rebuilds the egg example, then requires `git diff --exit-code -- examples/egg/ledger`: if you change anything that
affects the egg ledger, regenerate and commit it.

In a real project run `ledger.py` from the project root (where `ledger/` lives), not from inside `ledger/`.

## Style

- Prose in docs and help texts: plain, short sentences, no marketing; explain terms (Lean, `sorry`) for readers
  outside formal methods. Keep README, FORMAT.md and `--help` texts in sync with behaviour.
- Errors the user can fix raise `LedgerError` with a message that says what to do.
- Commit messages: a short subject, then a paragraph on what changed and why.
