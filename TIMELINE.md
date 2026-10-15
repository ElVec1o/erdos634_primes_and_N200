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

## Authorship

The research, the proofs and the formalization are by Vico Bonfioli, carried out throughout with the assistance of
Claude (Anthropic), which was used for exploration, computation, proof drafting and Lean development under the
author's direction.
