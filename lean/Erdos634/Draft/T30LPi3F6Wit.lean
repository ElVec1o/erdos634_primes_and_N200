import Mathlib.Tactic
import Erdos634.Draft.T30LPi3F6

/-!
# T30L stage 3(a): witness and control for `reflect_of_swapped` / `corner_chord_reflection`'s geometric step

Explicit coordinates of the rational `π/3` tile `(a,b,c) = (5,8,7)` (`c² = a²+b²−ab`, `7` opposite `π/3`): `P = (0,0)`, `Q = (7,0)`,
`X = (44/7, 20√3/7)` with `|PX| = 8`, `|QX| = 5`.  The hypotheses of `reflect_of_swapped` are satisfied by `X' = P+Q−X`; the mirror image
`M = (44/7, −20√3/7)` of `X` across `PQ` has the SAME legs `(8,5)` and is a different point, so the swapped-legs hypothesis
(from the fan count in `corner_chord_reflection`) is what selects the point reflection.
-/

namespace Erdos634.Pi3F6

open Erdos634.Geometry

noncomputable def pP : Plane := !₂[0, 0]
noncomputable def pQ : Plane := !₂[7, 0]
noncomputable def pX : Plane := !₂[44 / 7, 20 * Real.sqrt 3 / 7]
noncomputable def pM : Plane := !₂[44 / 7, -(20 * Real.sqrt 3 / 7)]

noncomputable def fy : Plane →ₗ[ℝ] ℝ := -((EuclideanSpace.proj 1 : Plane →L[ℝ] ℝ) : Plane →ₗ[ℝ] ℝ)

theorem s3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)

theorem dist_PX : dist pP pX = 8 := by
  have h : dist pP pX ^ 2 = 8 ^ 2 := by
    rw [dist_sq_coord]; simp [pP, pX]; nlinarith [s3]
  exact (sq_eq_sq₀ dist_nonneg (by norm_num)).mp h

theorem dist_QX : dist pQ pX = 5 := by
  have h : dist pQ pX ^ 2 = 5 ^ 2 := by
    rw [dist_sq_coord]; simp [pQ, pX]; nlinarith [s3]
  exact (sq_eq_sq₀ dist_nonneg (by norm_num)).mp h

theorem dist_PM : dist pP pM = 8 := by
  have h : dist pP pM ^ 2 = 8 ^ 2 := by
    rw [dist_sq_coord]; simp [pP, pM]; nlinarith [s3]
  exact (sq_eq_sq₀ dist_nonneg (by norm_num)).mp h

theorem dist_QM : dist pQ pM = 5 := by
  have h : dist pQ pM ^ 2 = 5 ^ 2 := by
    rw [dist_sq_coord]; simp [pQ, pM]; nlinarith [s3]
  exact (sq_eq_sq₀ dist_nonneg (by norm_num)).mp h

theorem pPQ : pP ≠ pQ := by
  intro h
  have := congrArg (fun z : Plane => z 0) h
  simp [pP, pQ] at this

theorem fy_apply (z : Plane) : fy z = -z 1 := by simp [fy]


theorem hX_neg : fy pX < 0 := by
  have hs : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  rw [fy_apply]; simp [pX]

/-- The reflected point has legs `(5, 8)` (swapped) and lies above the line. -/
theorem refl_props : 0 < fy (pP + pQ - pX) ∧ dist pP (pP + pQ - pX) = 5 ∧ dist pQ (pP + pQ - pX) = 8 := by
  have hs : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  refine ⟨?_, ?_, ?_⟩
  · rw [fy_apply]; simp [pX, pP, pQ]
  · have h : dist pP (pP + pQ - pX) ^ 2 = 5 ^ 2 := by
      rw [dist_sq_coord]; simp [pP, pQ, pX]; nlinarith [s3]
    exact (sq_eq_sq₀ dist_nonneg (by norm_num)).mp h
  · have h : dist pQ (pP + pQ - pX) ^ 2 = 8 ^ 2 := by
      rw [dist_sq_coord]; simp [pP, pQ, pX]; nlinarith [s3]
    exact (sq_eq_sq₀ dist_nonneg (by norm_num)).mp h

/-- **Witness.**  On the real `(5,8,7)` tile: any point `X''` above the line with legs `(5, 8)` (the swap of `X`'s `(8, 5)`) is
`P + Q − X` — `reflect_of_swapped` instantiated, with all hypotheses discharged (and `refl_props` shows such a point exists). -/
theorem wit_reflect (X'' : Plane) (hX'' : 0 < fy X'') (h1 : dist pP X'' = 5) (h2 : dist pQ X'' = 8) :
    X'' = pP + pQ - pX :=
  reflect_of_swapped fy 0 pPQ (by simp [fy_apply, pP]) (by simp [fy_apply, pQ]) hX_neg hX''
    (by rw [h1, dist_QX]) (by rw [h2, dist_PX])

/-- **Control.**  The mirror image `M` of `X` across `PQ` has the same legs `(8, 5)` as `X` and is NOT the point reflection
`P + Q − X`: legs alone do not determine the placement; the swap does. -/
theorem mirror_ne_reflect : pM ≠ pP + pQ - pX ∧ dist pP pM = dist pP pX ∧ dist pQ pM = dist pQ pX := by
  refine ⟨?_, by rw [dist_PM, dist_PX], by rw [dist_QM, dist_QX]⟩
  intro h
  have := congrArg (fun z : Plane => z 0) h
  simp [pM, pP, pQ, pX] at this
  norm_num at this

end Erdos634.Pi3F6

#print axioms Erdos634.Pi3F6.wit_reflect
#print axioms Erdos634.Pi3F6.mirror_ne_reflect
#print axioms Erdos634.Pi3F6.reflect_of_swapped
#print axioms Erdos634.Pi3F6.corner_chord_reflection
#print axioms Erdos634.Pi3F6.same_side_unique
