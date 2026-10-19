# Release v3.0 (paper version 3.0), 19 October 2026

Tag `v3.0` covers TWO papers, each of version 3.0: **Paper W** (`paper/erdos634_v3W.pdf`, 21 pp.: Tilings of W_M and T_M below the threshold scale, a six-piece template) and the **companion** (`paper/erdos634_v3C.pdf`, 21 pp.: Conjecture C, the collar family and the census of tile counts, with computer evidence). Both share one notation table (`paper/notation_table.tex`). The algebra of Theorem W is re-run by `code/check_thmW_algebra.py`. The version 2.2 paper and the first paper are unchanged.

**The prime case is unchanged. Nothing in this release bears on the prime case or on the base-beta question.** This release is about which counts are tile counts and at which scales; it adds a conjecture, a census update, and a list of corrections.

## What is new

1. **Theorem W** (Lean `Draft.ThmW.thmW`; proof, sign table and exact Lean/hand/computed accounting in Paper W). For coprime 2 <= e <= f-2 and an integer M with Me >= f and (M-1)(f-e) >= f, the triangle W_M(e,f) (sides Mf(f^2-e^2), Me(2f^2-e^2), Mf^3) is tiled by M^2(2f^2-e^2) copies of the tile (ef, f^2-e^2, f^2), and the isosceles triangle T_M(e,f) by M^2(3f^2-e^2). The tiling is a layout of six pieces whose scales are explicit functions of M and of n = floor(eM/f). For e < f/2 the condition Me >= f is sharp, because Me < f was excluded in an earlier release. So for e >= 2 the scale f is not the threshold: W_3(2,5) has 414 tiles, W_4(3,5) (sides 320, 492, 500) has 656. This closes the open case W_4(3,5) of the first paper and refutes the size conjecture (longest side >= c^2).
2. **Collar family** (Lean). (f^2-1)(2f^2-1) g^2 for all f >= 2, g >= f+1; 465 g^2 for g >= 5; 2485 g^2 and 966 g^2 for all g >= 2. The up-set in g and the form b(b+c)K^2 are D. Paliy's (2026-09-29); our construction is independent. The collar step with arbitrary height is a hand proof.
3. **27 more tile counts by macro pieces** (Lean): 375, 540, 735, 825, 630, 1120, 1750, 3864, 8694, 9940, 15456, 22365, 24150, 34776, 47334, 61824, 96600, 116886, 139104, 163254, 189336, 217350, 247296, 279174, 312984, 62125, 78246; twelve square multiples of template counts; the thirteen first W tilings below the scale f with closures. 97 exact tilings (`data/witnesses/v3_exact`, 26 MB), verified by the exact verifier of the repository (97/97).
4. **Conjecture C**: the set of tile counts is the union of explicit families (Table 1 of the paper); its existence half is a Lean theorem on the proved ranges, the exclusion half is open. Not claimed true.
5. **Census** (non-squarefree N <= 10^6): 199,140 excluded / 129,108 tile counts / 63,826 undecided (was 199,140 / 102,613 / 90,321). New tile counts by label: Lean 26,312; exact tiling only 145; hand 35; paper-formal closure 3. 134 values in families claimed by Paliy are not counted. Squarefree open: 770.
6. **W3+ census** (evidence only): for g = 3, all 191,940 (4,7) words and all 84,462 (5,8) words are refuted by exact search (conditional on the hand filters); (7,12) is 95.06% covered. No tiling found; not a proof.
7. **Corrections** (companion, Appendix E): 183 is not a tile count; for e >= 2 tilings exist below the scale f (the earlier "threshold = f" pattern is false); the claim that the template exists only when 4f < 9e is false; the size conjecture is false; Paliy's 4830 is a tiling (we had checked the wrong file); the theta statement "te >= f has no tiling" is false (the true bound is te >= 2f); the alpha up-set is Paliy's; two counts in notes.

## What is NOT proved (full list in Section 10 of the paper)

* The **exclusion half of Conjecture C**: no description of the set of tile counts above 200 is proved. 63,826 non-squarefree and 770 squarefree values up to 10^6 are undecided.
* The **no side of Theorem W for e > f/2**: for each row at most two scales M (those with (M-1)(f-e) < f < (M+1)(f-e)) are undecided. **e = 1 and e = f-1 for T_M** (first case T_3(1,4)); the T side in general (only 2Me < f is excluded).
* **V and A'** for gamma = 2 alpha (the W3+ evidence is not a proof; (7,12) is incomplete).
* **Theta and S3**: thresholds of the theta-isosceles family and the smallest scales of the base-alpha rows; the squarefree cores 465, 966, 2485 and the values 1860, 4185, 7440.
* **15 m^2 for every m >= 4 as a Lean theorem** (m = 5, 6, 7 are Lean `TileCount` statements; the Lean step `eqD_step` is not yet applied to them); the collar step for arbitrary height (hand); Paliy's claims beyond 4830.
* **An outside check.** All Lean statements, including `theoremP_6` (the prime case of earlier releases) and Theorem W, were compared with the mathematical statements and audited only inside this project. A reading by a person outside the project has not been made. Announcing the prime case as proved remains the author's decision.

## Credits

D. Paliy (alpha up-set 2026-09-29; W/beta framework and caps 2026-10-03; 990 on 2026-10-06; 264 on 2026-10-07; 15 m^2, 4830, mixed-corner family 2026-10-08; theta-isosceles family and scale additivity 2026-09-29); M. Beeson and G. Rosu (targets W, T, run-induction method, preprint of 2026-10-16); M. Beeson (2012 papers; seeds 84 and 189, Figures 28-29); B. Herdt (1125); M. Laczkovich (macro-dissections, classification of pairs); Y. X. Zhang (2 pi/3 families); J. P. Harries (88, 189); Snover, Waiveris and Williams (rep-tiles). Beeson's public withdrawal note of arXiv:2607.19572 (v2, 2026-09-24) credits V. Bonfioli; it is cited as public record. Details with dates: paper Section 11.

## AI disclosure

These results were obtained with the help of an AI system (Claude, Anthropic); the questions and directions were the author's, and the proofs are checked in Lean or by hand as labelled.

## Checks

* `lean/Erdos634/AllV3.lean`: 84 new modules built one at a time, no `sorry`, no `native_decide`, no axiom in the new modules; full build log 58,118 axiom lines, 0 failures.
* `lean/axioms/AxiomsAllV3.lean`: 98 declarations, each `[propext, Classical.choice, Quot.sound]` (`code/axiom_gate.py`: 98/98).
* `bte verify` on `data/witnesses/v3_exact/*.gz`: 97/97 VERIFIED (congruent, disjoint, area, hull is a triangle).
* Build resources: largest sampled `lean` about 5.4 GB; 22 GB of build products; one module at a time.

## Readability pass (2026-10-19), split into two papers
The single 30-page draft was split on the advice of every blind reader. **Paper W** (21 pp.) carries one idea: Theorem W, its T half, the refutation of the threshold-f expectation and of the size conjecture, the six-piece layout with worked examples (W_3(2,5)=414, W_4(3,5)=656, delta=1 case (2,5,5)), a proof with a table of every sign condition and a six-number 'sine table' that lets a reader redo any cross-product row, and a claims ledger (Lean / hand / computed / imported). **Companion**: collar family, macro pieces, Conjecture C, census, W3+ evidence, corrections; the proof of Theorem W is removed and cited.
Blind-reader loop on Paper W: 8 rounds (3 fresh readers each, plus an adversarial reader in 5 rounds). Real errors found and fixed along the way are recorded in `private/ROOM/READ_W/PROGRESS.md` (none in the mathematics after round 1; the adversary recomputed every example, the sign table, the sine table and the open-case claims). **Gate NOT met**: A=4 in every round, but B (notation before use) and C (following the proof) stay at 3 and E at 3-4; mean about 3.5, not 4.3. Companion: one reader round (A 4, B 3, C 2-3, D 3-4, E 3, F 3); fixes for labels (collar step blue, sharpness and T-tiling rows) applied, no further rounds. Scores are from AI readers (sonnet, haiku), not from mathematicians.
