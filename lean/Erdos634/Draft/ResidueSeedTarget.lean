/-
Draft/ResidueSeedTarget.lean -- the residue seed: the target `O A C` (determinant, sides, area), the model (sides, area)
and the third side of the target on the strips.

The construction is due to D. Paliy, "unrestricted all-scale positive theorem for W and beta" (2026, unrefereed).
Part of the formal proof in `Draft.ResidueSeed`; split off to keep each Lean process small.
No sorry, no native_decide.
-/
import Erdos634.Draft.ResidueBlocksDefs

open scoped Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open Erdos634.Geometry Erdos634.CertCoord
open Erdos634.Draft.CollarParam (Sh Rect RTiling.cast RTiling.castN interior_disj_fst interior_disj_snd)

namespace Erdos634.Draft.Residue
open Erdos634.Draft.WFrameF Erdos634.Draft.RegionTiling
open Erdos634.Draft.S2G (triC triC_pts carrier_triC brickL brickU brick_rt cong_U_cell grid scaledRT baseTri
  baseTri_cong vol_triC sq_Phi' dPhi' disjoint_image' f_ne)
open Erdos634.Draft.WBrickF (interior_disj_lin)
open Erdos634.Draft.CollarE1 (mapped_grid Pg)
open Erdos634.Draft.CollarG (φβ hφβ ca cb hapos hbpos hvpos hPpos WTilable)
open Erdos634.Draft.FDBBaseBetaE1 (HasSides hasSides_rot hasSides_swap)
open Erdos634.Draft.UniformThreshold (BetaTilable ThresholdAt hasSides_congr)

/-! ## The third side of the target on the strips -/

theorem hBnn {t r e : ℝ} (hu : 0 < t + r) (he : 0 < e) : 0 ≤ (t + r + e) ^ 2 - (t + r) ^ 2 := by
  linarith only [mul_pos he hu, sq_nonneg e]

/-- on the lower strips: `v Y − u X ≤ a b w` -/
theorem low_N {t r e X Y : ℝ} (hu : 0 < t + r) (he : 0 < e) (hY : Y ≤ (t + r + e) ^ 2 * (t + r) * t)
    (hL : -((t + r + e) * ((t + r) * (t + r + e)) * ((t + r + e) ^ 2 - (t + r) ^ 2))
      ≤ (t + r + e) * X - (t + r) * Y) :
    (t + r + e) * Y - (t + r) * X
      ≤ ((t + r) * (t + r + e)) * ((t + r + e) ^ 2 - (t + r) ^ 2) * ((t + r) + t) := by
  have hV : 0 < t + r + e := by linarith
  refine le_of_mul_le_mul_left ?_ hV
  linarith only [mul_nonneg hu.le (sub_nonneg.mpr hL), mul_nonneg (hBnn hu he) (sub_nonneg.mpr hY)]

/-- on the lower strips: `v³ X − u Q Y ≥ −a b c m` -/
theorem low_T {t r e X Y : ℝ} (ht : 0 < t) (hu : 0 < t + r) (he : 0 < e)
    (hY : Y ≤ (t + r + e) ^ 2 * (t + r) * t)
    (hL : -((t + r + e) * ((t + r) * (t + r + e)) * ((t + r + e) ^ 2 - (t + r) ^ 2))
      ≤ (t + r + e) * X - (t + r) * Y) :
    -(((t + r) * (t + r + e)) * ((t + r + e) ^ 2 - (t + r) ^ 2) * (t + r + e) ^ 2 * ((t + r + e) + t))
      ≤ (t + r + e) ^ 3 * X + (-((t + r) * (2 * (t + r + e) ^ 2 - (t + r) ^ 2))) * Y := by
  have hB := hBnn hu he
  have h3 : 0 ≤ ((t + r + e) ^ 2 - (t + r) ^ 2) * (t + r + e) ^ 2 * (t + r) * t * e :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hB (sq_nonneg _)) hu.le) ht.le) he.le
  linarith only [mul_nonneg (sq_nonneg (t + r + e)) (sub_nonneg.mpr hL),
    mul_nonneg (mul_nonneg hB hu.le) (sub_nonneg.mpr hY), h3]

/-- on the middle strips: `v³ X − u Q Y ≥ −a b c m` -/
theorem mid_T {t r e X Y : ℝ} (ht : 0 < t) (hu : 0 < t + r) (he : 0 < e)
    (hY : (t + r + e) ^ 2 * (t + r) * t ≤ Y)
    (hN : (t + r + e) * Y - (t + r) * X
      ≤ ((t + r) * (t + r + e)) * ((t + r + e) ^ 2 - (t + r) ^ 2) * ((t + r) + t)) :
    -(((t + r) * (t + r + e)) * ((t + r + e) ^ 2 - (t + r) ^ 2) * (t + r + e) ^ 2 * ((t + r + e) + t))
      ≤ (t + r + e) ^ 3 * X + (-((t + r) * (2 * (t + r + e) ^ 2 - (t + r) ^ 2))) * Y := by
  have hB := hBnn hu he
  have hV : 0 < t + r + e := by linarith
  have h3 : 0 ≤ ((t + r + e) ^ 2 - (t + r) ^ 2) * (t + r + e) ^ 2 * (t + r) ^ 2 * t * e :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hB (sq_nonneg _)) (sq_nonneg _)) ht.le) he.le
  refine le_of_mul_le_mul_left ?_ hu
  linarith only [mul_nonneg (pow_pos hV 3).le (sub_nonneg.mpr hN),
    mul_nonneg (sq_nonneg ((t + r + e) ^ 2 - (t + r) ^ 2)) (sub_nonneg.mpr hY), h3]

/-- on the triangle on top: `v³ X − u Q Y ≥ −a b c m` -/
theorem top_T {t r e X Y : ℝ} (hu : 0 < t + r) (he : 0 < e)
    (hY : Y ≤ (t + r + e) ^ 2 * (t + r + e) * (t + r + e + t)) (hL : 0 ≤ (t + r + e) * X - (t + r) * Y) :
    -(((t + r) * (t + r + e)) * ((t + r + e) ^ 2 - (t + r) ^ 2) * (t + r + e) ^ 2 * ((t + r + e) + t))
      ≤ (t + r + e) ^ 3 * X + (-((t + r) * (2 * (t + r + e) ^ 2 - (t + r) ^ 2))) * Y := by
  have hB := hBnn hu he
  linarith only [mul_nonneg (sq_nonneg (t + r + e)) hL, mul_nonneg (mul_nonneg hu.le hB) (sub_nonneg.mpr hY)]

/-! ## The target -/
section blocks
variable {t r e : ℝ} (ht : 0 < t) (hr : 0 < r) (he : 0 < e)
include ht hr he

theorem detT : ((pA t r e).1 - (pO t r e).1) * ((pC t r e).2 - (pO t r e).2)
    - ((pC t r e).1 - (pO t r e).1) * ((pA t r e).2 - (pO t r e).2)
    = (t + r) * (t + r + e) ^ 3 * ((t + r) ^ 2 + 4 * (t + r) * e + 2 * e ^ 2) * (t + r + e + t) ^ 2 := by
  have hb : e * (2 * t + 2 * r + e) ≠ 0 := by positivity
  simp only [pA, pO, pC]; field_simp; ring

/-- the target `O A C` -/
noncomputable def tgtT : Erdos634.Geometry.Tri :=
  triC (φβ (t + r) e) (hφβ (add_pos ht hr) he) (pO t r e) (pA t r e) (pC t r e)
    (by rw [detT ht hr he]; positivity)

theorem carrier_tgtT : (tgtT ht hr he).carrier = Phi (φβ (t + r) e) '' TT t r e := by
  unfold tgtT TT
  rw [carrier_triC]

theorem tgtT_sides :
    dist ((tgtT ht hr he).pts 0) ((tgtT ht hr he).pts 1)
      = (t + r) * ((t + r) ^ 2 + 4 * (t + r) * e + 2 * e ^ 2) * (t + r + e + t) ∧
    dist ((tgtT ht hr he).pts 1) ((tgtT ht hr he).pts 2) = (t + r + e) * (e * (2 * t + 2 * r + e)) * (t + r + e + t) ∧
    dist ((tgtT ht hr he).pts 0) ((tgtT ht hr he).pts 2) = (t + r + e) ^ 3 * (t + r + e + t) := by
  have hu := add_pos ht hr
  have hf := hφβ hu he
  have h1 : t + r ≠ 0 := hu.ne'
  have h2 : t + r + e ≠ 0 := by positivity
  have h3 : 3 * (t + r + e) ^ 2 - (t + r) ^ 2 ≠ 0 := (hPpos hu he).ne'
  have hb : e * (2 * t + 2 * r + e) ≠ 0 := by positivity
  simp only [tgtT, triC_pts, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  refine ⟨?_, ?_, ?_⟩
  · refine (sq_eq_sq₀ dist_nonneg (by positivity)).mp ?_
    rw [sq_Phi' hf]; simp only [pO, pA, φβ]; field_simp; ring
  · refine (sq_eq_sq₀ dist_nonneg (by positivity)).mp ?_
    rw [sq_Phi' hf]; simp only [pA, pC, φβ]; field_simp; ring
  · refine (sq_eq_sq₀ dist_nonneg (by positivity)).mp ?_
    rw [sq_Phi' hf]; simp only [pO, pC, φβ]; field_simp; ring

open MeasureTheory in
theorem vol_tgtT : volume (tgtT ht hr he).carrier
    = ENNReal.ofReal (|sD (φβ (t + r) e) / (2 * φβ (t + r) e)|
        * ((t + r) * (t + r + e) ^ 3 * ((t + r) ^ 2 + 4 * (t + r) * e + 2 * e ^ 2) * (t + r + e + t) ^ 2))
      * volume Erdos634.AreaDet.stdCarrier := by
  unfold tgtT
  rw [vol_triC]
  congr 2
  rw [abs_mul]
  congr 1
  rw [detT ht hr he, abs_of_pos (by positivity)]

end blocks

section model
variable {u e : ℝ} (hu : 0 < u) (he : 0 < e)
include hu he

theorem ModC_sides : dist ((ModC hu he).pts 0) ((ModC hu he).pts 1) = ca u e ∧
    dist ((ModC hu he).pts 1) ((ModC hu he).pts 2) = (u + e) ^ 2 ∧
    dist ((ModC hu he).pts 0) ((ModC hu he).pts 2) = cb u e := by
  have hf := hφβ hu he
  have h1 : u ≠ 0 := hu.ne'
  have h2 : u + e ≠ 0 := (hvpos hu he).ne'
  have h3 : 3 * (u + e) ^ 2 - u ^ 2 ≠ 0 := (hPpos hu he).ne'
  simp only [ModC, brickL, triC_pts, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  refine ⟨?_, ?_, ?_⟩
  · refine (sq_eq_sq₀ dist_nonneg (hapos hu he).le).mp ?_
    rw [sq_Phi' hf]; ring
  · refine (sq_eq_sq₀ dist_nonneg (hc2 hu he).le).mp ?_
    rw [sq_Phi' hf]; ring
  · refine (sq_eq_sq₀ dist_nonneg (hbpos hu he).le).mp ?_
    rw [sq_Phi' hf]; simp only [ca, cb, φβ]; field_simp; ring

open MeasureTheory in
theorem volModC : volume (ModC hu he).carrier
    = ENNReal.ofReal (|sD (φβ u e) / (2 * φβ u e)| * (ca u e * (u + e) ^ 2))
      * volume Erdos634.AreaDet.stdCarrier := by
  unfold ModC Erdos634.Draft.S2G.brickL
  rw [vol_triC]
  congr 2
  rw [abs_mul]
  congr 1
  have hE : ((ca u e, (0 : ℝ)).1 - ((0 : ℝ), (0 : ℝ)).1) * ((ca u e, (u + e) ^ 2).2 - ((0 : ℝ), (0 : ℝ)).2)
      - ((ca u e, (u + e) ^ 2).1 - ((0 : ℝ), (0 : ℝ)).1) * ((ca u e, (0 : ℝ)).2 - ((0 : ℝ), (0 : ℝ)).2)
      = ca u e * (u + e) ^ 2 := by ring
  rw [hE, abs_of_pos (mul_pos (hapos hu he) (hc2 hu he))]

end model

end Erdos634.Draft.Residue
