# Roadmap and parked ideas

## Planned (agreed order)
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
