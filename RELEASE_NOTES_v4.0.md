# Release v4.0, 22 October 2026

A positive integer N is a tile count if some triangle can be cut into N pairwise congruent triangles (Erdős Problem 634). **The problem is not solved here.** Nothing below has been checked by anyone outside the project; all Lean statements and proofs were compared and audited inside the project only.

## What is new since v3.1 (with labels)

1. **Band theorem (Lean, internal audit, no outside check).** For coprime 2 <= e < f and M >= 2 with f <= 2Me < f + e, the isosceles triangle T_M(e,f) has no dissection into congruent copies of the tile (ef, f^2 - e^2, f^2) (`Erdos634.LaczJunction.Walk.band_theorem_free`; also the cases 2Me - f <= 1 and <= 2, `no_tiling_U`, `no_tiling_U2`). Axioms: `propext`, `Classical.choice`, `Quot.sound` only; no `sorry`. The statement, the arithmetic and the axioms were audited by fresh sessions of the same model family (verdict: sound, with gaps that are limits of the audit's scope; no defect found); two line-by-line reads of the geometric induction found no error. **No reader outside the project has checked the Lean statement against the mathematical one or read the proof.** Not covered: instances with 2Me - f >= e (M < f; 19,151 census values), and e = 1 (39 values).
2. **Registry extract.** 3,204 single instances (e, f, M) of the base-beta family are excluded by those three Lean theorems; they are listed in `data/registry/registry_basebeta_NO_TILING_4.0.tsv` (counts: band theorem 2,535; `no_tiling_U` 448; `no_tiling_U2` 221). Each row is an instance, not a value of N. The file is a curated extract; the working registry is not part of this release.
3. **Census update (program output, not a Lean theorem about each N).** Non-squarefree N <= 10^6 (392,074 values): **199,364 -> 200,282 excluded (+918)**; undecided 63,593 -> **62,421**. The smallest newly excluded value is 1,964, so nothing changes below 1,000. The count of known tile counts is **not printed** for this version: it changed since v3.1 through sweep results and registry rows that have not all been rechecked value by value against exact verification and Paliy's repository, and none of them is claimed here. An N counts as excluded when every failing leaf of the exclusion chain is killed by a registry row; the leaf model is the census program's, as in earlier releases. Controls (three synthetic negative controls and a baseline reproduction of the previous census) pass; the 918 values agree with an independent count.
4. **Formalization of published triangle-tiling results** (Laczkovich, Beeson, Zhang) continues in a separate public repository, "Formalizing triangle tiling in Lean" (github.com/ElVec1o/formalizing-triangle-tiling-in-lean, commit `d728130`, version 1.0). The Lean files of the band theorem and of everything it imports are there, not here: `Erdos634/Draft/LaczFormalMJFinal.lean` (`band_theorem_free`), `LaczFormalUDims.lean` (`no_tiling_U`), `LaczFormalW2Walk.lean` (`no_tiling_U2`), the aggregate `Draft/AllLaczWalk.lean`, and their imports (`LaczFormalGraph*`, `LaczFormalBand*`, `LaczFormalMJ*`). This release does not rebuild them. Nothing else from that repository is claimed here.

## The prime case (unchanged result, dates)
- The Lean theorem `theoremP_6` (no prime p congruent to 3 (mod 4), p > 3, is a tile count) was published in our release of 15 October 2026 (Zenodo, doi:10.5281/zenodo.23400433, version of that date). It was audited only inside the project; no outside check has been made.
- D. Paliy made a proof public on 29 September 2026 (repository DenisUkranian/erdos-634-tilings; no change seen since 17 October 2026); our proof was obtained independently.
- M. Beeson and G. Rosu, arXiv:2607.23453, versions 2 (16 October 2026) and 3 (21 October 2026), state a result on the prime tile counts. We claim nothing about their proof.
- The prime theorem is stated and machine-checked in the author's Lean development, published in the release of 15 October 2026; internal audits only, no outside check; the author makes no claim beyond that. These are parallel works.

## What did not change
Every N <= 200 is decided; the base-beta family at scale M with f/(2e) < M < f is open beyond what is stated above; the full problem is open.

## Not claimed
- No claim of outside verification, of a classification, or of the full problem.
- New tile counts from searches that have not passed an exact recheck and a comparison with Paliy's repository are not claimed.
- Search certificates and the engines are not part of this release (certificate export off); no program sources for the census are included.

## Checks
- The Lean modules of the band theorem were built in the author's working repository; they were **not rebuilt here**, and are not part of this repository (see item 4). The earlier aggregates of this repository (All, AllSpectrum, AllThreshold, AllV3, AllV3b, AllV3c) are unchanged by this release.
- The companion paper (`paper/erdos634_v3C.pdf`) was compiled from source with no undefined references.

## Credits
M. Beeson and G. Rosu (the tile and targets, vertex-figure lemmas, run-induction method), D. Paliy (alpha up-set 2026-09-29; W/beta framework; dated items as in v3.0 and v3.1), B. Herdt, Y. X. Zhang, M. Laczkovich (fans and chord covers; classification), J. P. Harries. The band induction and the registry aggregation are ours.

## AI disclosure
These results were obtained with the help of an AI system (Claude, Anthropic); the questions and directions were the author's; proofs are checked in Lean or by hand as labelled.

## Citation
Concept DOI (all versions): 10.5281/zenodo.23400433. This version: DOI to be filled after the Zenodo record exists. Previous: v3.1 10.5281/zenodo.23488114; v3.0 10.5281/zenodo.23483290.
