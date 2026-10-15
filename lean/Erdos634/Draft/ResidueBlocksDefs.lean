/-
Draft/ResidueBlocksDefs.lean -- generated file; do not edit by hand.

Frame geometry of the three outside blocks and of the target of the residue seed of the member `(u, v)` at the scale
`m = v + t`: `u = t + r`, `v = t + r + e` (`t, r, e > 0`), in the coordinates `(X, Y)` of the frame `Φ_φ`,
`φ = φβ u e` (cell `a × c`).  Points, lattice vectors, the five block regions `B1a, B1b, B2a, B2b, B3`, the target
`TT = O A C`.  The linear bounds that separate the blocks from each other and from the strips of the hexagon and
put them inside the target are in the modules `Draft.ResidueBlocksB1a`, `…B1b`, `…B2a`, `…B2b`, `…B3`, `…TT`
(one module per region, so that each fits in memory); `Draft.ResidueBlocks` imports them all.

The construction is due to D. Paliy, "unrestricted all-scale positive theorem for W and beta" (2026, unrefereed).
No sorry, no native_decide.
-/
import Erdos634.Draft.ResidueTools

open scoped Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open Erdos634.Geometry Erdos634.CertCoord

namespace Erdos634.Draft.Residue
open Erdos634.Draft.S2L (hull_le hull_ge mem_hull3')
open Erdos634.Draft.CollarE1 (Pg)

noncomputable def vS (t r e : ℝ) : ℝ × ℝ := ((-2 * t * e - 2 * r * e - e ^ 2), (0))
noncomputable def vE (t r e : ℝ) : ℝ × ℝ := (((-t ^ 4 - 4 * t ^ 3 * r - 4 * t ^ 3 * e - 6 * t ^ 2 * r ^ 2 - 12 * t ^ 2 * r * e - 6 * t ^ 2 * e ^ 2 - 4 * t * r ^ 3 - 12 * t * r ^ 2 * e - 12 * t * r * e ^ 2 - 4 * t * e ^ 3 - r ^ 4 - 4 * r ^ 3 * e - 6 * r ^ 2 * e ^ 2 - 4 * r * e ^ 3 - e ^ 4) / (e * (2 * t + 2 * r + e))), ((-t ^ 4 - 4 * t ^ 3 * r - 3 * t ^ 3 * e - 6 * t ^ 2 * r ^ 2 - 9 * t ^ 2 * r * e - 3 * t ^ 2 * e ^ 2 - 4 * t * r ^ 3 - 9 * t * r ^ 2 * e - 6 * t * r * e ^ 2 - t * e ^ 3 - r ^ 4 - 3 * r ^ 3 * e - 3 * r ^ 2 * e ^ 2 - r * e ^ 3) / (e * (2 * t + 2 * r + e))))
noncomputable def vS2 (t r e : ℝ) : ℝ × ℝ := ((t ^ 2 + 2 * t * r + t * e + r ^ 2 + r * e), (t ^ 2 + 2 * t * r + 2 * t * e + r ^ 2 + 2 * r * e + e ^ 2))
noncomputable def vE2 (t r e : ℝ) : ℝ × ℝ := (((-t ^ 4 - 4 * t ^ 3 * r - 3 * t ^ 3 * e - 6 * t ^ 2 * r ^ 2 - 9 * t ^ 2 * r * e - 3 * t ^ 2 * e ^ 2 - 4 * t * r ^ 3 - 9 * t * r ^ 2 * e - 6 * t * r * e ^ 2 - t * e ^ 3 - r ^ 4 - 3 * r ^ 3 * e - 3 * r ^ 2 * e ^ 2 - r * e ^ 3) / (e * (2 * t + 2 * r + e))), ((-t ^ 4 - 4 * t ^ 3 * r - 2 * t ^ 3 * e - 6 * t ^ 2 * r ^ 2 - 6 * t ^ 2 * r * e - t ^ 2 * e ^ 2 - 4 * t * r ^ 3 - 6 * t * r ^ 2 * e - 2 * t * r * e ^ 2 - r ^ 4 - 2 * r ^ 3 * e - r ^ 2 * e ^ 2) / (e * (2 * t + 2 * r + e))))
noncomputable def pQ0 (t r e : ℝ) : ℝ × ℝ := ((-2 * t ^ 3 * e - 6 * t ^ 2 * r * e - 3 * t ^ 2 * e ^ 2 - 6 * t * r ^ 2 * e - 6 * t * r * e ^ 2 - t * e ^ 3 - 2 * r ^ 3 * e - 3 * r ^ 2 * e ^ 2 - r * e ^ 3), (0))
noncomputable def pS (t r e : ℝ) : ℝ × ℝ := ((t ^ 4 + 3 * t ^ 3 * r - t ^ 3 * e + 3 * t ^ 2 * r ^ 2 - 4 * t ^ 2 * r * e - 3 * t ^ 2 * e ^ 2 + t * r ^ 3 - 5 * t * r ^ 2 * e - 6 * t * r * e ^ 2 - t * e ^ 3 - 2 * r ^ 3 * e - 3 * r ^ 2 * e ^ 2 - r * e ^ 3), (t ^ 4 + 3 * t ^ 3 * r + 2 * t ^ 3 * e + 3 * t ^ 2 * r ^ 2 + 4 * t ^ 2 * r * e + t ^ 2 * e ^ 2 + t * r ^ 3 + 2 * t * r ^ 2 * e + t * r * e ^ 2))
noncomputable def pP0 (t r e : ℝ) : ℝ × ℝ := (((-t ^ 6 - 5 * t ^ 5 * r - 4 * t ^ 5 * e - 10 * t ^ 4 * r ^ 2 - 16 * t ^ 4 * r * e - 10 * t ^ 4 * e ^ 2 - 10 * t ^ 3 * r ^ 3 - 24 * t ^ 3 * r ^ 2 * e - 34 * t ^ 3 * r * e ^ 2 - 12 * t ^ 3 * e ^ 3 - 5 * t ^ 2 * r ^ 4 - 16 * t ^ 2 * r ^ 3 * e - 42 * t ^ 2 * r ^ 2 * e ^ 2 - 32 * t ^ 2 * r * e ^ 3 - 6 * t ^ 2 * e ^ 4 - t * r ^ 5 - 4 * t * r ^ 4 * e - 22 * t * r ^ 3 * e ^ 2 - 28 * t * r ^ 2 * e ^ 3 - 11 * t * r * e ^ 4 - t * e ^ 5 - 4 * r ^ 4 * e ^ 2 - 8 * r ^ 3 * e ^ 3 - 5 * r ^ 2 * e ^ 4 - r * e ^ 5) / (e * (2 * t + 2 * r + e))), ((-t ^ 6 - 5 * t ^ 5 * r - 3 * t ^ 5 * e - 10 * t ^ 4 * r ^ 2 - 12 * t ^ 4 * r * e - 3 * t ^ 4 * e ^ 2 - 10 * t ^ 3 * r ^ 3 - 18 * t ^ 3 * r ^ 2 * e - 9 * t ^ 3 * r * e ^ 2 - t ^ 3 * e ^ 3 - 5 * t ^ 2 * r ^ 4 - 12 * t ^ 2 * r ^ 3 * e - 9 * t ^ 2 * r ^ 2 * e ^ 2 - 2 * t ^ 2 * r * e ^ 3 - t * r ^ 5 - 3 * t * r ^ 4 * e - 3 * t * r ^ 3 * e ^ 2 - t * r ^ 2 * e ^ 3) / (e * (2 * t + 2 * r + e))))
noncomputable def pR0 (t r e : ℝ) : ℝ × ℝ := (((t ^ 5 * e + 4 * t ^ 4 * r * e - 4 * t ^ 4 * e ^ 2 + 6 * t ^ 3 * r ^ 2 * e - 16 * t ^ 3 * r * e ^ 2 - 10 * t ^ 3 * e ^ 3 + 4 * t ^ 2 * r ^ 3 * e - 24 * t ^ 2 * r ^ 2 * e ^ 2 - 28 * t ^ 2 * r * e ^ 3 - 6 * t ^ 2 * e ^ 4 + t * r ^ 4 * e - 16 * t * r ^ 3 * e ^ 2 - 26 * t * r ^ 2 * e ^ 3 - 11 * t * r * e ^ 4 - t * e ^ 5 - 4 * r ^ 4 * e ^ 2 - 8 * r ^ 3 * e ^ 3 - 5 * r ^ 2 * e ^ 4 - r * e ^ 5) / (e * (2 * t + 2 * r + e))), ((t ^ 5 * e + 4 * t ^ 4 * r * e + 3 * t ^ 4 * e ^ 2 + 6 * t ^ 3 * r ^ 2 * e + 9 * t ^ 3 * r * e ^ 2 + 3 * t ^ 3 * e ^ 3 + 4 * t ^ 2 * r ^ 3 * e + 9 * t ^ 2 * r ^ 2 * e ^ 2 + 6 * t ^ 2 * r * e ^ 3 + t ^ 2 * e ^ 4 + t * r ^ 4 * e + 3 * t * r ^ 3 * e ^ 2 + 3 * t * r ^ 2 * e ^ 3 + t * r * e ^ 4) / (e * (2 * t + 2 * r + e))))
noncomputable def pV (t r e : ℝ) : ℝ × ℝ := ((2 * t ^ 4 + 7 * t ^ 3 * r + 2 * t ^ 3 * e + 9 * t ^ 2 * r ^ 2 + 5 * t ^ 2 * r * e + 5 * t * r ^ 3 + 4 * t * r ^ 2 * e + r ^ 4 + r ^ 3 * e), (2 * t ^ 4 + 7 * t ^ 3 * r + 4 * t ^ 3 * e + 9 * t ^ 2 * r ^ 2 + 10 * t ^ 2 * r * e + 2 * t ^ 2 * e ^ 2 + 5 * t * r ^ 3 + 8 * t * r ^ 2 * e + 3 * t * r * e ^ 2 + r ^ 4 + 2 * r ^ 3 * e + r ^ 2 * e ^ 2))
noncomputable def pO (t r e : ℝ) : ℝ × ℝ := (((-2 * t ^ 6 - 11 * t ^ 5 * r - 9 * t ^ 5 * e - 25 * t ^ 4 * r ^ 2 - 41 * t ^ 4 * r * e - 16 * t ^ 4 * e ^ 2 - 30 * t ^ 3 * r ^ 3 - 74 * t ^ 3 * r ^ 2 * e - 58 * t ^ 3 * r * e ^ 2 - 14 * t ^ 3 * e ^ 3 - 20 * t ^ 2 * r ^ 4 - 66 * t ^ 2 * r ^ 3 * e - 78 * t ^ 2 * r ^ 2 * e ^ 2 - 38 * t ^ 2 * r * e ^ 3 - 6 * t ^ 2 * e ^ 4 - 7 * t * r ^ 5 - 29 * t * r ^ 4 * e - 46 * t * r ^ 3 * e ^ 2 - 34 * t * r ^ 2 * e ^ 3 - 11 * t * r * e ^ 4 - t * e ^ 5 - r ^ 6 - 5 * r ^ 5 * e - 10 * r ^ 4 * e ^ 2 - 10 * r ^ 3 * e ^ 3 - 5 * r ^ 2 * e ^ 4 - r * e ^ 5) / (e * (2 * t + 2 * r + e))), ((-2 * t ^ 6 - 11 * t ^ 5 * r - 7 * t ^ 5 * e - 25 * t ^ 4 * r ^ 2 - 32 * t ^ 4 * r * e - 9 * t ^ 4 * e ^ 2 - 30 * t ^ 3 * r ^ 3 - 58 * t ^ 3 * r ^ 2 * e - 33 * t ^ 3 * r * e ^ 2 - 5 * t ^ 3 * e ^ 3 - 20 * t ^ 2 * r ^ 4 - 52 * t ^ 2 * r ^ 3 * e - 45 * t ^ 2 * r ^ 2 * e ^ 2 - 14 * t ^ 2 * r * e ^ 3 - t ^ 2 * e ^ 4 - 7 * t * r ^ 5 - 23 * t * r ^ 4 * e - 27 * t * r ^ 3 * e ^ 2 - 13 * t * r ^ 2 * e ^ 3 - 2 * t * r * e ^ 4 - r ^ 6 - 4 * r ^ 5 * e - 6 * r ^ 4 * e ^ 2 - 4 * r ^ 3 * e ^ 3 - r ^ 2 * e ^ 4) / (e * (2 * t + 2 * r + e))))
noncomputable def pA (t r e : ℝ) : ℝ × ℝ := ((2 * t ^ 4 + 7 * t ^ 3 * r + 5 * t ^ 3 * e + 9 * t ^ 2 * r ^ 2 + 13 * t ^ 2 * r * e + 4 * t ^ 2 * e ^ 2 + 5 * t * r ^ 3 + 11 * t * r ^ 2 * e + 7 * t * r * e ^ 2 + t * e ^ 3 + r ^ 4 + 3 * r ^ 3 * e + 3 * r ^ 2 * e ^ 2 + r * e ^ 3), (2 * t ^ 4 + 7 * t ^ 3 * r + 3 * t ^ 3 * e + 9 * t ^ 2 * r ^ 2 + 8 * t ^ 2 * r * e + t ^ 2 * e ^ 2 + 5 * t * r ^ 3 + 7 * t * r ^ 2 * e + 2 * t * r * e ^ 2 + r ^ 4 + 2 * r ^ 3 * e + r ^ 2 * e ^ 2))
noncomputable def pC (t r e : ℝ) : ℝ × ℝ := ((2 * t ^ 4 + 7 * t ^ 3 * r + 5 * t ^ 3 * e + 9 * t ^ 2 * r ^ 2 + 13 * t ^ 2 * r * e + 4 * t ^ 2 * e ^ 2 + 5 * t * r ^ 3 + 11 * t * r ^ 2 * e + 7 * t * r * e ^ 2 + t * e ^ 3 + r ^ 4 + 3 * r ^ 3 * e + 3 * r ^ 2 * e ^ 2 + r * e ^ 3), (2 * t ^ 4 + 7 * t ^ 3 * r + 7 * t ^ 3 * e + 9 * t ^ 2 * r ^ 2 + 18 * t ^ 2 * r * e + 9 * t ^ 2 * e ^ 2 + 5 * t * r ^ 3 + 15 * t * r ^ 2 * e + 15 * t * r * e ^ 2 + 5 * t * e ^ 3 + r ^ 4 + 4 * r ^ 3 * e + 6 * r ^ 2 * e ^ 2 + 4 * r * e ^ 3 + e ^ 4))
noncomputable def pE1 (t r e : ℝ) : ℝ × ℝ := (((-t ^ 6 - 6 * t ^ 5 * r - 5 * t ^ 5 * e - 15 * t ^ 4 * r ^ 2 - 25 * t ^ 4 * r * e - 10 * t ^ 4 * e ^ 2 - 20 * t ^ 3 * r ^ 3 - 50 * t ^ 3 * r ^ 2 * e - 40 * t ^ 3 * r * e ^ 2 - 10 * t ^ 3 * e ^ 3 - 15 * t ^ 2 * r ^ 4 - 50 * t ^ 2 * r ^ 3 * e - 60 * t ^ 2 * r ^ 2 * e ^ 2 - 30 * t ^ 2 * r * e ^ 3 - 5 * t ^ 2 * e ^ 4 - 6 * t * r ^ 5 - 25 * t * r ^ 4 * e - 40 * t * r ^ 3 * e ^ 2 - 30 * t * r ^ 2 * e ^ 3 - 10 * t * r * e ^ 4 - t * e ^ 5 - r ^ 6 - 5 * r ^ 5 * e - 10 * r ^ 4 * e ^ 2 - 10 * r ^ 3 * e ^ 3 - 5 * r ^ 2 * e ^ 4 - r * e ^ 5) / (e * (2 * t + 2 * r + e))), ((-t ^ 6 - 6 * t ^ 5 * r - 4 * t ^ 5 * e - 15 * t ^ 4 * r ^ 2 - 20 * t ^ 4 * r * e - 6 * t ^ 4 * e ^ 2 - 20 * t ^ 3 * r ^ 3 - 40 * t ^ 3 * r ^ 2 * e - 24 * t ^ 3 * r * e ^ 2 - 4 * t ^ 3 * e ^ 3 - 15 * t ^ 2 * r ^ 4 - 40 * t ^ 2 * r ^ 3 * e - 36 * t ^ 2 * r ^ 2 * e ^ 2 - 12 * t ^ 2 * r * e ^ 3 - t ^ 2 * e ^ 4 - 6 * t * r ^ 5 - 20 * t * r ^ 4 * e - 24 * t * r ^ 3 * e ^ 2 - 12 * t * r ^ 2 * e ^ 3 - 2 * t * r * e ^ 4 - r ^ 6 - 4 * r ^ 5 * e - 6 * r ^ 4 * e ^ 2 - 4 * r ^ 3 * e ^ 3 - r ^ 2 * e ^ 4) / (e * (2 * t + 2 * r + e))))
noncomputable def pE2 (t r e : ℝ) : ℝ × ℝ := (((-t ^ 6 - 5 * t ^ 5 * r - 3 * t ^ 5 * e - 10 * t ^ 4 * r ^ 2 - 12 * t ^ 4 * r * e - 7 * t ^ 4 * e ^ 2 - 10 * t ^ 3 * r ^ 3 - 18 * t ^ 3 * r ^ 2 * e - 25 * t ^ 3 * r * e ^ 2 - 9 * t ^ 3 * e ^ 3 - 5 * t ^ 2 * r ^ 4 - 12 * t ^ 2 * r ^ 3 * e - 33 * t ^ 2 * r ^ 2 * e ^ 2 - 26 * t ^ 2 * r * e ^ 3 - 5 * t ^ 2 * e ^ 4 - t * r ^ 5 - 3 * t * r ^ 4 * e - 19 * t * r ^ 3 * e ^ 2 - 25 * t * r ^ 2 * e ^ 3 - 10 * t * r * e ^ 4 - t * e ^ 5 - 4 * r ^ 4 * e ^ 2 - 8 * r ^ 3 * e ^ 3 - 5 * r ^ 2 * e ^ 4 - r * e ^ 5) / (e * (2 * t + 2 * r + e))), ((-t ^ 6 - 5 * t ^ 5 * r - 2 * t ^ 5 * e - 10 * t ^ 4 * r ^ 2 - 8 * t ^ 4 * r * e - t ^ 4 * e ^ 2 - 10 * t ^ 3 * r ^ 3 - 12 * t ^ 3 * r ^ 2 * e - 3 * t ^ 3 * r * e ^ 2 - 5 * t ^ 2 * r ^ 4 - 8 * t ^ 2 * r ^ 3 * e - 3 * t ^ 2 * r ^ 2 * e ^ 2 - t * r ^ 5 - 2 * t * r ^ 4 * e - t * r ^ 3 * e ^ 2) / (e * (2 * t + 2 * r + e))))

/-- block 1, the triangle `Q0, uv·e, X` (the tile at scale `uv`, lattice `(s, e)`) -/
noncomputable def B1a (t r e : ℝ) : Set (ℝ × ℝ) := convexHull ℝ {pQ0 t r e, pE1 t r e, ((0 : ℝ), (0 : ℝ))}
/-- block 1, the parallelogram of `uv × ut` cells `a × c` -/
noncomputable def B1b (t r e : ℝ) : Set (ℝ × ℝ) :=
  Pg (pE1 t r e) (((t + r) * (t + r + e)) • (vS t r e - vE t r e)) (((t + r) * t) • vE t r e)
/-- block 2, the triangle `Q0, Q0 + ut·e2, S` (the tile at scale `ut`, lattice `(s2, e2)`) -/
noncomputable def B2a (t r e : ℝ) : Set (ℝ × ℝ) := convexHull ℝ {pQ0 t r e, pE2 t r e, pS t r e}
/-- block 2, the parallelogram of `dt × ut` cells `a × c` -/
noncomputable def B2b (t r e : ℝ) : Set (ℝ × ℝ) :=
  Pg (pE2 t r e) ((e * t) • vE2 t r e) (((t + r) * t) • (vS2 t r e - vE2 t r e))
/-- block 3, the triangle `V, R0, C` (the tile at scale `K`) -/
noncomputable def B3 (t r e : ℝ) : Set (ℝ × ℝ) := convexHull ℝ {pV t r e, pR0 t r e, pC t r e}
/-- the target `O A C` -/
noncomputable def TT (t r e : ℝ) : Set (ℝ × ℝ) := convexHull ℝ {pO t r e, pA t r e, pC t r e}

end Erdos634.Draft.Residue
