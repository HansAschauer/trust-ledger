# Architecture: a fixed core, adapters per field

trust-ledger started with machine-checked mathematics (Lean, ProVerif), but the question it answers is the
same in every field: *which exact statements of a paper rest on what, who vouches for them, and what has
changed since?* A map in a GIS paper, a measured value in an experiment and a preregistered effect in a
psychology study all fit this pattern. This document says which parts are fixed and which are meant to
vary.

## The core (`ledger.py`, normative in `FORMAT.md`)

Same in every field, and kept small:

* nodes, canonical JSON, SHA-256, the Merkle DAG, the root, lock files, `verify`;
* the two hashes of a node: `full` (everything) and `spec` (what it *states*). Attestations bind to
  `spec`, so evidence can be refreshed without resetting them, while a changed statement resets them;
* claims, `uses`, scopes per paper, attestations (stale or current), optional signatures;
* the register: what a claim ultimately rests on that no machine checked (assertions, cited results,
  hypotheses, unproved steps, models whose faithfulness is a judgement).

The core stays a single file with no dependencies beyond the Python standard library. It never runs
field-specific tools during `status`, `lock` or `verify`; those read dumps and files only.

## What varies, and where it plugs in

| varies by field | mechanism | state |
|---|---|---|
| extracting evidence from tools | adapter dumps (`FORMAT.md` 2.6), written by any program | done; Lean and ProVerif use it |
| which part is statement, which evidence | the adapter's `spec` per node kind | done |
| open items a field cares about | the adapter's `register` items (`hyp:` makes a hypothesis) | done |
| status words shown per claim | the adapter's `status` and `word` | done; table columns still fixed (Lean, ProVerif) |
| data, steps, checks (no tool of its own) | built-in kinds `source`, `step`, `check`; salted commitments | done (`examples/lab`) |
| evidence vocabulary (E1 to E5 for mathematics) | a table in `ledger.toml`, E1 to E5 as default | planned |
| checklists for attesting persons | per node kind, in `ledger.toml` | planned |
| the paper (LaTeX now) | a paper adapter: claim id to statement text | planned |

Why dumps and not a plugin API: adapters can be written in the language of the field (R, Matlab, Lean,
shell), the core stays one file, and an adapter cannot get the hashing wrong because it never hashes
anything that the core recomputes.

## Writing an adapter

1. Decide what a reference looks like (`model.pv#query`, `fit/g`, `table3/row5`). Claims list
   references under the adapter's name.
2. Decide, per node kind, what goes into `content` (everything that should make the root change) and
   what goes into `spec` (only what should reset attestations when it changes). If in doubt, leave
   `spec` out: then every change resets attestations, which is the safe default.
3. Map the tool's outcome to `status` (`ok`, `conditional` = holds given hypotheses, `open`, `failed`) and a
   short `word` for the table.
4. Emit `register` items for what the tool cannot check (the faithfulness of a model, a manual step, a
   deviation from a preregistration).
5. Read references on stdin, write the dump on stdout, exit non-zero on failure. Configure it as
   `[adapter.NAME] extract = "..."`. `adapters/proverif.py` is a complete example in about 70 lines;
   `adapters/lean.py` shows a converter that sits behind a tool's own exporter (`Dump.lean`).

## `verify` and `reproduce`

`verify` recomputes all hashes from the dumps and files in the repository and compares them with the lock
file: cheap, and needs no field-specific tools. Rerunning the tools themselves (`extract`, later
`reproduce` for steps) checks that the dumps are what the tools produce; it needs Lean, ProVerif, R, QGIS
and so on. Readers who only want to know whether anything changed since publication need the first.

## Test for the design

Every field we claim to support gets a toy example under `examples/` that runs in the test suite. If one
of them needs a change to the core, the abstraction is wrong and the core changes, not the example.
