# Example: how long should I boil my egg?

A short paper (`paper/main.tex`) with an evidence ledger behind it. The physics comes from
D. Buay et al., *How long does it take to boil an egg? Revisited*, Eur. J. Phys. 27 (2006) 119–131.
The kitchen, its data, the authors A. Cook and B. Taster, and the reader C. Reader are fictitious.

    make           # extract, check, lock, tex, then the PDF (paper/main.pdf, appendix "Evidence ledger")
    make verify    # recompute the root; check the standalone attestation against the lock
    make reproduce # re-run the fit in a scratch copy and compare its output
    python3 ../../ledger.py -P egg status
    python3 ../../ledger.py -P egg why fridge

| result | evidence | attestations |
|---|---|---|
| Lemma 1 `lem:firstorder` (Buay et al., eq. 11) | hypothesis `Egg.FirstOrder`, cited | green, signed (A. Cook): a known result, checklist H1–H3 |
| Lemma 2 `lem:scaling` (bigger eggs) | Lean | green, signed (A. Cook); green, signed by an outside reader in a standalone file (`ledger/reader-attestation.toml`) |
| Lemma 3 `lem:colder` (colder eggs) | Lean | green (B. Taster), **stale**: given for an earlier, weaker version (≤), before the lemma was sharpened to < |
| Theorem 4 `thm:fridge` (one minute more from the fridge) | Lean, given Lemma 1 | green, signed (A. Cook); yellow, unsigned, with a reason (B. Taster) |
| Lemma 5 `lem:altitude` | none | not in the ledger: the appendix lists it as not covered |
| Observation 6 `obs:kitchen` | data → manual step → script → check | green, signed (A. Cook) |
| Observation 7 `obs:taste` | tasting notes, salted commitment (notes and salt published here as a demonstration) | green, unsigned (B. Taster) |
| Conjecture 8 `conj:six` | an assertion | conjecture, signed (A. Cook) |

What is real and what is not:

* `formal/Egg.lean` was checked with Lean 4 and Mathlib (standard axioms only). The ledger reads a hand-made
  Dump.lean output with its statements (`ledger/lean-dump.json`), so the example runs without Lean.
* `data/probe.csv` is synthetic: `scripts/synthesize.py` made it from the model plus noise. The ledger says so
  in the source's note.
* `private/tasting.txt` and its salt would never be published in a real project: the ledger records only the
  salted commitment, and only someone who is given notes and salt can check it. They are published here so
  that you can: `status` checks them against the commitment, and changing one character in the notes makes
  it an error. The example keys in `private/keys/` stay private (git-ignored), so nobody can add signatures
  in these people's names.
* `ledger/attestations.toml`, `ledger/keys.toml` and `ledger/lock-egg.json` are committed, unlike in the other
  examples. They were made with `ledger.py attest` / `addkey` / `lock`, never edited by hand.
