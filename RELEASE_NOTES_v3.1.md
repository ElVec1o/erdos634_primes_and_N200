# Release v3.1 (paper version 3.0 unchanged), 20 October 2026

A follow-up to v3.0. **No paper is rewritten**; the new material is a Lean aggregate, a census update and a short note, `docs/ADDENDUM_v3.1.md`. The prime case is unchanged: no prime p congruent to 3 (mod 4) with p > 3 is a tile count. Nothing here bears on the prime case or on the base-beta question.

## What is new (with labels)

1. **Lean, new aggregate `Erdos634.AllV3c`** (77 new source modules; sources only):
   * `Draft/NSQWinAll`, `Draft/NSQWin*`: `no_dissection_win`, the 67 census-excluded values N <= 10^5 (270, 412, 750, 963, 1470, 2430, ..., 97470) have no congruent dissection, by a windowed, divisor-bounded version of the leaf checks of the exclusion chain (kernel `decide`, one declaration per leaf). **UNAUDITED** (not read by anyone outside the project). Negative/positive controls: `Draft/NSQWinCtl6` (the chain does not fire at the known tile counts 63, 72, 143, 320, 375, 540, 1029, 1860, 4185, 7440, and fires at 270 and 412).
   * `Draft/CollarFam465` with seed `Draft/TM1860`: **465 g^2 is a tile count for every g >= 2** (Lean; this replaces the exact-only status of g = 2, 3, 4 in v3.0). The core 465 (g = 1) is open.
   * `Draft/CollarFam59` with seed `Draft/TM30688`: **7672 g^2 is a tile count for every g >= 2** (tile (45,56,81), row (5,9); Lean). Paliy's up-set already covers g with K >= 153 for this row; the small-g range g = 2..152 is ours. The core 7672 (g = 1) is not covered.
   * Everything else the aggregate needs (chain lemma, thick regime, `CollarFam2`, `no_dissection_412`, `no_dissection_270`) was already in v3.0 (`AllV3`, `AllV3b`).
   * **Where it was built.** The modules were built in the author's working repository (one module at a time, no `sorry`, no `native_decide`); they were NOT rebuilt in this repository (disk). Sources were copied with project-internal paths removed from comments; the 1,061 shared modules in their closure that differ from the earlier public copies differ in comments only (checked by a comment-stripping comparison). The 15 axiom lines in `lean/axioms/AxiomsAllV3c.lean` were printed in the working repository: all `[propext, Classical.choice, Quot.sound]`. A reader who rebuilds here should expect the same, but that rebuild has not been done by us.
2. **Census** (non-squarefree N <= 10^6, 392,074 values; census program version 1.5.5, controls pass on the registry as of v3.0): **199,364 excluded / 129,117 tile counts / 63,593 undecided**; with the hand-proved Theorem R2 class (separate row): 199,441 / 129,117 / 63,516. Change from v3.0: 129,108 -> 129,117 known (+3 for 465 g^2: 1860, 4185, 7440, now Lean; +6 for 7672 g^2: 30688, 69048, 122752, 191800, 276192, 375928), undecided 63,602 -> 63,593. Of the 199,364 exclusions, **67 are Lean-formal** (the list above); the other 199,297 are census-level (hand or computed legs, not formalized).
3. **Rung e+3 of the thick regime (computer-assisted case tree; NOT a theorem).** A case tree for the rung M(f-e) = e+3 was run for the 26 census triples with f <= 40 (and for all 370 coprime pairs with f <= 40): 9,990 of 9,990 certificates were verified by an independent exact verifier. It is not machine-checked end to end, not in Lean, and not read by anyone outside the project; the hand legs have one reader of the same model family; f > 40 is untouched (f = 41..60 only partly done). If it were accepted it would exclude 10 further values with f <= 40 (956, 2108, 2852, 3906, 4676, 8334, 22768, 24350, 30352, 51793), which are NOT counted in the census above. The trusted items are listed in `docs/ADDENDUM_v3.1.md`. The engine sources are not part of this release.
4. **Not claimed.** New tile counts found by the overnight sweep that have not passed an exact recheck and a check against Paliy's repository are not claimed (see the addendum, "Candidates").

## Checks
* `lean/axioms/AxiomsAllV3c.lean`: 15 declarations, standard axioms only (printed in the working repository).
* The v3.0 checks stand (AllV3, AllV3b, 100/100 exact tilings).
* Paliy's repository (DenisUkranian/erdos-634-tilings) was re-read on 2026-10-20: head 0f7935b (2026-10-17), unchanged since v3.0.

## Credits
M. Beeson and G. Rosu (targets W, T; run-induction method), M. Beeson, D. Paliy (alpha up-set 2026-09-29; W/beta framework 2026-10-03; further dated items as in v3.0), B. Herdt, Y. X. Zhang, M. Laczkovich, J. P. Harries.

## AI disclosure
These results were obtained with the help of an AI system (Claude, Anthropic); the questions and directions were the author's; proofs are checked in Lean or by hand as labelled.
