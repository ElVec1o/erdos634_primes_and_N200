# Addendum to release v3.0, in release v3.1 (20 October 2026)

This note is short on purpose; the papers are those of v3.0. Labels: LEAN = theorem of the library with standard axioms only; HAND = written proof, read only inside the project; COMPUTED = exact computation, no proof; CLAIMED = Paliy's.

## 1. New Lean (aggregate `Erdos634.AllV3c`)
| Item | Statement | Label |
|---|---|---|
| `NSQWinAll.no_dissection_win` | no congruent dissection with N tiles for the 67 values of `winList` (all <= 10^5, including 270, 412, 750, 963) | LEAN, unaudited, controls `NSQWinCtl6` |
| `CollarFam465.tileCount_465_sq_ge2` | 465 g^2 is a tile count for g >= 2 (1860, 4185, 7440, ...) | LEAN |
| `CollarFam59.tileCount_7672_sq_ge2` | 7672 g^2 is a tile count for g >= 2 (30688, 69048, ...); Paliy's up-set covers K >= 153 | LEAN |
Built in the author's working repository, not rebuilt here (see the release notes); sources only.

## 2. Census, non-squarefree N <= 10^6
Excluded / tile counts / undecided = 199,364 / 129,117 / 63,593. Separate hand-proved row (Theorem R2): 199,441 / 129,117 / 63,516. Lean-formal exclusions: 67 (all <= 10^5). Squarefree undecided: unchanged from v3.0 (about 770; not recounted).

## 3. Rung e+3 (not a theorem)
Setting: W_M(e,f) with e >= 2, M < f, Me >= f and M(f-e) = e+3. A case tree starting at the corner (four branches according to the first two runs, with the lattice hypothesis for the third level removed by computation) was run for the 26 census triples with f <= 40: 9,990 of 9,990 local certificates verified by an independent exact verifier; 0 rejected, 0 alive. For f in 41..60, 653 of 672 verified (partial). Items that are trusted, not proved:
1. The local search/verifier model: the closed-wedge rules, the reading of the partition condition with clamped ends, shared by solver and verifier (same rule semantics), completeness of the six first placements, independence of the irrationality (Niven) input.
2. Only the base and the second side at the corner are modelled; the third side is not. A missing wall can only open stretches, so it cannot create a false kill; the minimal distance from every window centre to the third side exceeds the window radius by at least 6.77 tile-units (floating point, margin about six orders above the rounding error).
3. 24 gap kills at d = 4: the stretch length is e(f-e) = a+b-c, which is smaller than each of a, b, c, so it is not a sum of edges (arithmetic, hand); which lattice points bound the stretch is read from the certificate.
4. The statement that the first tile of the next level is the lattice tile is a computed fact for the range, not a hypothesis; but the contexts imposed by the case tree and the finite windows are limitations of what is searched.
5. The half of the case tree about a single long c-run reduces to calls of size at most e (hand, with a Lean lemma K).
Missing: f > 40, any Lean proof, an outside read. Not counted in the census; if accepted it would exclude 956, 2108, 2852, 3906, 4676, 8334, 22768, 24350, 30352, 51793 (f <= 40). No source of the verifier or the solver is released.

## 4. Candidates (NOT claimed)
An overnight search for further tile counts produced exact tilings for the following values, which have not been rechecked by the release verifier and have not been compared with Paliy's repository or the census; some may already be known: 544, 26180, 38070, 48664, 51520, 58905, 69524, 70040, 78804, 83328, 90820, 94920, 104720, 105750, 109494, 111384, 115080, 115680, 115920, 125188, 156429, 157590, 160664, 163625, 164164, 177309, 187488, 194656, 196833, 206080, 207270, 210560, 213570, 220440, 235620, 248584. They are listed so that nobody repeats the search; they are not results of this release.

## 5. Unchanged
The prime case; Conjecture C (existence half only); the corrections list of v3.0; the residual issues of v3.0 (no outside reader for theoremP_6, Theorem W, the thick rungs or Theorem R2).
