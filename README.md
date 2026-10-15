# Tile counts of triangles: the primes and every N ≤ 200, formalized in Lean 4

**Author:** Vico Bonfioli (vicobonfioli@gmail.com). The work was carried out with the assistance of Claude (Anthropic)
throughout; see the acknowledgements of the paper.
**Status:** pre-release, private. The paper, the Lean development and the reproduction instructions are being added;
this file will be regenerated from the paper before release.

## Abstract

An integer N is a *tile count* if some triangle can be cut into N pairwise congruent triangles; Erdős asked for the
set of tile counts (Problem #634). We prove, with every step checked in Lean 4 against the standard axioms only, that a
prime p is a tile count if and only if p = 3 or p ≢ 3 (mod 4), and we determine the tile counts N ≤ 200.

## Main results

1. **Primes.** A prime p is a tile count if and only if p = 3 or p ≢ 3 (mod 4). Label: VERIFIED (Lean theorem
   `TheoremP6.theoremP_6` for the exclusions; constructions for the existence half).
2. **N ≤ 200.** For 1 ≤ N ≤ 200, N is a tile count if and only if N is one of 105 explicit values: the numbers of the
   forms k², 3k², 6k², x² + y² (x, y ≥ 1), 7m² and 11m² (m ≥ 2), together with 77, 84, 88, 126, 143 and 189.
   Label: VERIFIED (exclusions by kernel-checked certificates; existence by explicit tilings).

Theorem numbers and the Lean map table will be added with the paper.

## Files

| Path | Purpose |
|---|---|
| `README.md` | this index |
| `TIMELINE.md` | dated record of the results and of their public and pre-release copies |
| `LICENSE` | CC BY 4.0 for the text, MIT for the code |
