# Roadmap and parked ideas

## Planned (agreed order)

Done 2026-10-08: all five steps (signatures via ssh-keygen, key nodes, standalone attestation files); steps 1 to 3 (per-paper scopes, paper source and statements from LaTeX, generated root/status
files + `ledgercheck.sty`, tested by compiling a real paper), and the environment globs / stale-dump guard of step 4.
1. Per-paper scoping (`--paper`), one root per paper.
2. Paper source as a node (all `.tex`/`.bib` reached from main, minus generated ledger files);
   claim statement text extracted from the theorem environment carrying the claim's `\label`.
3. Generated, `\input`ed root file per paper + `ledger status` appendix/table via the sty (a draft build
   without the file prints an "unsealed draft" marker). All generated files live under one path that the
   source hash excludes. The root file records the source hash it was computed over.
4. Non-blocking publish step: only "ledger cannot describe the release truthfully" (extraction fails,
   dump older than sources) fails; stale/unattested/sorry/assumes are shown, never block.
   `status --strict` stays opt-in for CI. `environment.files` accepts globs.
5. Optional signatures: `ssh-keygen -Y sign/verify`, namespace `trust-ledger-attestation`, keys as ledger
   nodes (introduced by the paper, by vouching, or by a recorded source URL), unsigned attestations stay
   valid. Post-publication attestations as small signed files checked by `verify-attestation`.
   Open: is `ssh-keygen` acceptable as the v1 dependency?

## Next: adapters for other fields (agreed 2026-10-11, see ARCHITECTURE.md)

1. Generic adapter dump in `FORMAT.md` 2.6. **Done.**
2. ProVerif on the adapter dump (`adapters/proverif.py`); hashes of existing ledgers unchanged. **Done.**
3. Lean on the adapter dump (`adapters/lean.py` converts the `Dump.lean` output). **Done**, as format 0.2.0:
   the hashes changed once (no Lean-specific rule left in the core); `migrate` rebinds attestations.
4. Built-in kinds `source` (external data pinned by hash, URL/DOI, retrieval date), `step` (inputs to
   outputs, a command or a manual step with a person; manual steps enter the register) and `check` (a
   command whose recorded result supports a claim). Salted hashes (commitments) for data that must not be
   published, since a plain hash of a small or guessable file reveals it. **Done** (part of format 0.2.0,
   additive), with `examples/lab`.
5. Evidence vocabulary and checklists configurable in `ledger.toml` (E1 to E5 as the default profile);
   one status column per adapter in `status` and `ledgercheck.sty` instead of fixed Lean/ProVerif columns.
   **Done.** (The review packet is still Lean-centred: back-translations of Lean statements.)
6. Toy examples for a lab measurement and a preregistered study, in the test suite; DVC/Snakemake import
   as a step adapter; `reproduce`.

## Parked ideas
### Signed disagreement (negative attestations)
An attestation with a negative outcome, e.g. "I checked claim X at spec hash H and the formal statement
does not match the text", signed with the reviewer's key. This would make *disagreement* a first-class,
checkable object instead of an email or a blog post, and it fits verification bounties (a successful
challenge is as valuable as a confirmation). Questions for later:
* an extra level value (`dispute`?) with a mandatory reason, and what a dispute is bound to (spec hash, so
  it dies when the statement changes?);
* how authors respond (a signed reply node linked to the dispute; resolved / acknowledged / rejected);
* how the appendix displays open disputes (they must not be hideable by the authors: disputes published
  outside the root, e.g. by the reviewer, cannot be removed by a later version);
* the sybil / identity problem is the same as for confirmations.
