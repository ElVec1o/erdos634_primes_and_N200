# Timeline of the work

This file records when each result of this repository was obtained and where a dated copy of it can be found. Two
kinds of dates appear. **Public** dates are those of a public GitHub commit or of a Zenodo record, both timestamped by a
third party. **Development** dates are commit dates of the author's working repository; they are recorded by the
author's own machine and are listed for completeness, with the first external copy of each named where one exists.

Notation: a *tile count* is an integer N such that some triangle can be cut into N pairwise congruent triangles
(Erdős Problem #634). For coprime 1 ≤ e < f, the *base-β target* T_M(e,f) is the isosceles triangle with legs Mf³ and
base Me(3f²−e²), tiled by copies of the triangle (ef, f²−e², f²); a prime count forces the scale M = 1.

## Public record

| Date (UTC) | Record | Content |
|---|---|---|
| 2026-06-27 | GitHub [ElVec1o/erdos_634_proof](https://github.com/ElVec1o/erdos_634_proof), first commit `488a36d3` | Signed-direction tiling functional; no prime number of tiles with a 2π/3 angle (irrational other angles) tiles an isosceles, non-equilateral triangle. |
| 2026-07-07 to 2026-07-10 | same repository, commits `a0133fb9`, `2c8d24b9` | The arithmetic and combinatorial layer of the argument checked in Lean 4. |
| 2026-06-27 to 2026-08-31 | Zenodo, concept record [10.5281/zenodo.20961918](https://doi.org/10.5281/zenodo.20961918), versions 1.0 (2026-06-27) to 3.0 | Successive versions of the preprint and its Lean development. |
| 2026-09-10 | Zenodo v3.1, [10.5281/zenodo.22690471](https://doi.org/10.5281/zenodo.22690471) | |
| 2026-09-12 06:28 | Zenodo v3.2, [10.5281/zenodo.22721069](https://doi.org/10.5281/zenodo.22721069) | Contains the Lean theorem `E1BaseWord.e1_family_f_ge_3_congruent`: no tiling of the base-β target T_1(1,f), f ≥ 3, so no prime of the form 3f² − 1 ≥ 26 is a tile count (47, 107, 191, …). |
| 2026-09-13 | GitHub `erdos_634_proof`, last public commit `4bb61193` | State of the public preprint: primes ≡ 3 (mod 4) excluded except the class ≡ 11 (mod 12), which reduces to the scale-one base-β targets T_1(e,f); the family e = 1 is excluded in Lean. |
| 2026-09-29 15:10 | GitHub `DenisUkranian/erdos-634-tilings`, commit `0730aafe` (D. Paliy) | First public proof of the prime case: no tiling of T_1(e,f) or W_1(e,f) for any member, by a column induction at scale one, and the deduction that a prime p is a tile count iff p = 2, 3 or p ≡ 1 (mod 4). |

## Corrections to releases v1.5 to v1.9.1 (stated in v1.10)

* The non-squarefree census of v1.5 to v1.9.1 (59,881 excluded / 101,566 known / 230,627 undecided for the 392,074 non-squarefree N <= 10^6) added 5,908 values excluded by Corollary thickw(a) to the formal count. That corollary is proved in the paper and is not formalized. Formal figures with all families of v1.10: 53,973 excluded / 102,471 known / 235,630 undecided; thickw(a) excludes a further 5,908 (sound, not exhaustive).
* The sentence "every undecided value fails the branch gamma = 2 alpha" was false (27,812 of the 230,627 do not). Correct: 203,146 of the 236,962 values left by the conditions fail the branch, and for 39,216 it is the only obstruction.
* Squarefree open values for N <= 10^6: 803 (a stopping-bound bug in the S2 sieve had omitted two known values).

## Pre-release (private)

| Date (UTC) | Record | Content |
|---|---|---|
| 2026-10-12 09:42 | Private GitHub repository of the author (not public), first snapshot (source commit `787c2ded`) | The full development of 26 September to 12 October 2026 listed below: papers, Lean formalization, verification code and data. Later snapshots record each further result with its source commit. |

## Development record (working repository)

The proof of the prime case in this repository was obtained independently of Paliy's, by different arguments
at scale one, and was kept private until its publication here; the commits below record its course.

| Date | Source commit | Result |
|---|---|---|
| 2026-09-27 | `e9d9e6fe` | Lean theorem `BaseBetaFullUnc.basebeta_full_unc`: no tiling of the base-β target T_1(e,f) for any coprime 1 ≤ e < f (built on 2026-09-26, committed the next day), with `R1Final.r1_no_tiling` for the members e = f − 1. |
| 2026-09-27 | `6ba8326c`, `69894fc6` | Lean assembly `TheoremP6.theoremP_6` of the exclusion of every prime N ≡ 3 (mod 4), N > 3, with five hypotheses left open. |
| 2026-09-30 | `270a3064` | `theoremP_6` with no hypotheses: in Lean, no prime N ≡ 3 (mod 4) with N > 3 is a tile count. |
| 2026-10-06 | `5d9b7d8a` (recorded 2026-10-08) | Internal audit of `theoremP_6`: the Lean statement matched against the mathematical statement; dependencies read in full. |
| 2026-10-09 to 2026-10-11 | several | Every N ≤ 104 decided in Lean; the tiling of the triangle (39, 49, 55) by 143 copies of (3, 5, 7) found and kernel-checked (`594d54cb`). |
| 2026-10-14 | `de4280e1` | 135 is not a tile count (kernel-checked certificate); with it, every N ≤ 200 is decided in Lean. |
| 2026-10-18 | `51d017de` | Non-squarefree census with the pi/3 pair leaf and the formal thickw(a): 71,039 excluded / 102,471 known / 218,564 undecided (N <= 10^6); release v1.11. |
| 2026-10-18 | working repository (hand proofs, no Lean) | Theorems C and D' and Lemma K for the gamma = 2 alpha target T(g): no tiling if (g-1)(v-u) < u, g >= 2; W_2 and Conjecture A' for d = 1; written proofs, audited twice inside the project, not formalized; release v1.12. |
| 2026-10-18 | release v1.12.1 (paper-only correction) | Correction: the v1.12 hand-level census of Theorems C and D' undercounted (older label dump). Correct: 74,158 of the 74,697 values failing only gamma = 2 alpha are D'-covered (C alone 64,961), 539 not; hand-level triple 145,197 / 102,471 / 144,406; formal triple unchanged. |
| 2026-10-18 | release v1.12.2 (paper, README and docstrings only) | Attribution update: credits to Beeson-Rosu (Lemmas 30, 32, 33, 34, Theorem 37), Paliy (60, 312) and others made explicit. No mathematical change. |
| 2026-10-18 | release v1.13 | Theorem D' (hence Theorem C, W_2, A' for d = 1) formalized in Lean (`ThmD.thmDStatement_geo`, about 105 modules); final chain `not_tile_of_conditionsNSQzETWD` with the word leaf; census of the non-squarefree N <= 10^6: 199,140 excluded / 102,471 known / 90,463 undecided. Method credited to Beeson-Rosu. |
| 2026-10-18 | release v1.13.1 | Correction of the census wording: of the 199,140 excluded, 196,273 satisfy the hypothesis of the single Lean theorem `ThmDChainW.not_tile_of_conditionsNSQzETWD`, 2,867 need in addition the sharpening 2Me < f combined by the program (v1.13 had 62,150 / 136,990, the older chain CN'zET). |
| 2026-10-18 | release v1.14 | Theorem D' for every g >= 1 (g = 1 reproduces Beeson 2012, Thm 11.7); all 199,140 non-squarefree exclusions from one Lean theorem (`not_tile_of_conditionsNSQzETWDS`); 204 and 228 excluded also by search certificates (reproduction); 22 R8 values are tile counts by exact verification of Paliy's layouts, 345 and 506 kernel-checked; squarefree open <= 10^6: 771 (exact) / 791 (Lean). |


## Authorship

The research, the proofs and the formalization are by Vico Bonfioli, carried out throughout with the assistance of
Claude (Anthropic), which was used for exploration, computation, proof drafting and Lean development under the
author's direction.
| 2026-10-18 | release v2.0 | Self-contained readable paper (34 pp) replaces the first paper (kept as `_v1`); records Theorem D' for every g >= 1, the single theorem for 199,140 exclusions, 204/228 certificates, 22 R8 tile counts, squarefree open 771/791; adds docs/TALK.md, docs/FAQ.md and a reading record. |
| 2026-10-19 | release v1.15 | Paliy's nested-corner family theorems formalized (`PRevAll.prev_family`, `PF2All.pf2_family`, `PF3All.pf3_family`, aggregate AllR8; constructions Paliy's, Lean proofs ours): all 22 R8 values are Lean theorems, squarefree open 771 at both levels; +134 non-squarefree tile counts by family + scaling (not individually formal); 13 template-search tilings (8 <= 10^6, 5 above), exact-verified, not Lean; census 199,140 / 102,613 / 90,321; paper version 2.1. Prime case unchanged. |
| 2026-10-19 | release v1.16 | Eight template tile counts (11625, 66960, 119040, 121765, 167865, 186000, 364560, 603750) are Lean theorems (`LadderFam`, `T<N>`, `AllTemplates` in AllR8; our engine, Beeson-Rosu III Thm 10 layer, Laczkovich-type macro dissections, Paliy's families); W3+ census at g = 3 for (4,7), (5,8), (7,12) recorded as evidence only (not a proof, not a refutation); paper version 2.2. Prime case unchanged. |
| 2026-10-19 | `383575f3`, `9a61b7bc` | Lean: existence half of Conjecture C (`ConjC/Defs`, `ConjC/Exist`, `conjC_existence`); twelve square multiples of template counts (`TemplateSquares`). |
| 2026-10-19 | `3b2058be`, `0e7b7c50`, `b6f1496f` | Lean: the thirteen W_M(e,f) tilings with M < f (656, 1312, 1648, 1825, 1953, 2192, 3088, 3296, 3775, 3824, 4068, 4450, 7889) and their upward closure in M (`AllWBelow`, `AllDebtB`); the first tilings below the scale f for e >= 2. |
| 2026-10-19 | `edec527f` | Lean: collar layer step and parametric seed for e = 1 (`CollarUp.tileCount_e1_up`): (f^2-1)(2f^2-1) g^2, g >= f+1; 465 g^2 (g >= 5). Paliy's alpha up-set is dated 2026-09-29 and is credited; the construction is independent. |
| 2026-10-19 | `02b0769e` | Lean: macro-piece bridge (`MacroPiece`) and 26 tile counts (375, 540, 735, 825, 630, 1120, 1750, the 966 g^2 chain to 279174, 9940, 22365, 62125); lowered tails 2485 g^2 (g >= 5) and 966 g^2 (g >= 17); with the smaller values 966 g^2 and 2485 g^2 hold for all g >= 2. |
| 2026-10-19 | `0304e9a8` | Lean: Theorem W (`Draft.ThmW.thmW`): W_M(e,f) and T_M(e,f) tile for coprime 2 <= e <= f-2 when Me >= f and (M-1)(f-e) >= f; sharp for e < f/2. Hand proof audited sound by a separate reader and by exact computation (4.8 million admissible triples checked against the proved exclusions, no conflict); Lean statement audited internally (match). |
| 2026-10-20 | release v3.0 | Papers version 3.0 (`paper/erdos634_v3W2.pdf`, `paper/erdos634_v3C.pdf`): Theorem W, collar family, macro-piece counts, Conjecture C, thick-regime no-tiling theorems (Lean for M(f-e) <= e+1; hand proof R2 for e+2), 465 g^2 for g = 2, 3, 4 by exact tilings, census 199,364 / 129,108 / 63,602 (non-squarefree N <= 10^6; 199,441 / 129,108 / 63,525 with the hand class R2), W3+ evidence, corrections (183 is not a tile count; scale f is not the threshold for e >= 2; size conjecture refuted by W_4(3,5)), what is not proved. Aggregates `Erdos634.AllV3` and `AllV3b` (all axioms standard), 100 exact tilings in `data/witnesses/v3_exact`. Prime case unchanged. |
