/-
Draft/S5N320.lean -- the isosceles triangle `(120, 120, 80)` is cut into `320` congruent triangles with sides `(6, 5, 9)`.

    theorem s5_8_2_3_tiling : ∃ D : CongruentDissection 320, (six side lengths)
    theorem s5_8_2_3 : ∃ D : CongruentDissection 320, HasSides D.target 120 120 80 ∧ HasSides D.model 5 9 6
    theorem not_S5Inst_8_2_3 : ¬ S5Inst 8 2 3

The target has base angles `α + β` and apex `α` for the tile `(6, 5, 9)` (`3α + 2β = π`, member `(e, f) = (2, 3)`): it
is the instance `(t, e, f) = (8, 2, 3)` of the row `N = t² (f² − e²)`.  So the instance statement `S5Inst 8 2 3`
("no dissection") is false.  The tiling was found by the search `rust/mrv2`, snapped to `ℤ[√2]/9`, verified exactly and
by the Lean kernel (`R320Tiling`).

`320 = 16² + 8²` is a tile count for a classical reason: this file adds an instance, not a number.
Prior art: D. Paliy's notes give the necessary form `N = b T²` for this target type and announce eventual existence for
every primitive tile.  No sorry, no native_decide.
-/
import Erdos634.R320TilingBridge
import Erdos634.Realizable
import Erdos634.Draft.RAInst
import Erdos634.Draft.HasSidesPerm

open scoped Classical
open Erdos634.Geometry

namespace Erdos634.Draft.S5N320
open Erdos634.Draft.FDBBaseBetaE1 (HasSides)

theorem eq_of_sq {d c : ℝ} (hd : 0 ≤ d) (hc : 0 < c) (h : d ^ 2 = c ^ 2) : d = c := by
  have h2 : (d - c) * (d + c) = 0 := by linear_combination h
  rcases mul_eq_zero.mp h2 with h3 | h3
  · linarith
  · linarith

open Erdos634.Realizable in
/-- **The tiling, with its six side lengths.** -/
theorem s5_8_2_3_tiling :
    ∃ D : CongruentDissection 320,
      dist (D.target.pts 0) (D.target.pts 1) = 80 ∧ dist (D.target.pts 1) (D.target.pts 2) = 120 ∧
      dist (D.target.pts 2) (D.target.pts 0) = 120 ∧
      dist (D.model.pts 0) (D.model.pts 1) = 6 ∧ dist (D.model.pts 1) (D.model.pts 2) = 5 ∧
      dist (D.model.pts 2) (D.model.pts 0) = 9 := by
  obtain ⟨D, t1, t2, t3, m1, m2, m3⟩ := Erdos634.R320TilingBridge.r320_dissection_shape
  have hν : (0 : ℝ) < 1 / 9 := by norm_num
  set Ds := scaleDissection (D.model.pts 0) (1 / 9) hν.ne' D with hDs
  have htd : ∀ i j : Fin 3,
      dist (Ds.target.pts i) (Ds.target.pts j) = 1 / 9 * dist (D.target.pts i) (D.target.pts j) := by
    intro i j
    rw [hDs, scaleDissection_target_pts, scaleDissection_target_pts, homothetyEquiv_dist, abs_of_pos hν]
  have hmd : ∀ i j : Fin 3,
      dist (Ds.model.pts i) (Ds.model.pts j) = 1 / 9 * dist (D.model.pts i) (D.model.pts j) := by
    intro i j
    rw [hDs, scaleDissection_model_pts, scaleDissection_model_pts, homothetyEquiv_dist, abs_of_pos hν]
  have T01 : dist (D.target.pts 0) (D.target.pts 1) = 720 :=
    eq_of_sq dist_nonneg (by norm_num) (by rw [t1]; norm_num)
  have T12 : dist (D.target.pts 1) (D.target.pts 2) = 1080 :=
    eq_of_sq dist_nonneg (by norm_num) (by rw [t2]; norm_num)
  have T20 : dist (D.target.pts 2) (D.target.pts 0) = 1080 :=
    eq_of_sq dist_nonneg (by norm_num) (by rw [t3]; norm_num)
  have M01 : dist (D.model.pts 0) (D.model.pts 1) = 54 :=
    eq_of_sq dist_nonneg (by norm_num) (by rw [m1]; norm_num)
  have M12 : dist (D.model.pts 1) (D.model.pts 2) = 45 :=
    eq_of_sq dist_nonneg (by norm_num) (by rw [m2]; norm_num)
  have M20 : dist (D.model.pts 2) (D.model.pts 0) = 81 :=
    eq_of_sq dist_nonneg (by norm_num) (by rw [m3]; norm_num)
  refine ⟨Ds, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [htd, T01]; norm_num
  · rw [htd, T12]; norm_num
  · rw [htd, T20]; norm_num
  · rw [hmd, M01]; norm_num
  · rw [hmd, M12]; norm_num
  · rw [hmd, M20]; norm_num

/-- the same in the form `HasSides` -/
theorem s5_8_2_3 : ∃ D : CongruentDissection 320, HasSides D.target 120 120 80 ∧ HasSides D.model 5 9 6 := by
  obtain ⟨D, t01, t12, t20, m01, m12, m20⟩ := s5_8_2_3_tiling
  exact ⟨D, ⟨Equiv.refl _, by simpa using t12, by simpa using t20, by simpa using t01⟩,
    ⟨Equiv.refl _, by simpa using m12, by simpa using m20, by simpa using m01⟩⟩

theorem rot0 : (finRotate 3).symm 0 = 2 := by decide
theorem rot1 : (finRotate 3).symm 1 = 0 := by decide
theorem rot2 : (finRotate 3).symm 2 = 1 := by decide

/-- **The instance statement `S5Inst 8 2 3` is false.** -/
theorem not_S5Inst_8_2_3 : ¬ Erdos634.Draft.NSQM.S5Inst 8 2 3 := by
  intro h
  obtain ⟨D, t01, t12, t20, m01, m12, m20⟩ := s5_8_2_3_tiling
  refine h D ?_ ?_ ?_ ⟨(finRotate 3).symm, ?_, ?_, ?_⟩
  · show dist (D.target.pts (0 + 1)) (D.target.pts (0 + 2)) = _
    rw [show ((0 : Fin 3) + 1) = 1 from rfl, show ((0 : Fin 3) + 2) = 2 from rfl, t12]; norm_num
  · show dist (D.target.pts (1 + 1)) (D.target.pts (1 + 2)) = _
    rw [show ((1 : Fin 3) + 1) = 2 from rfl, show ((1 : Fin 3) + 2) = 0 from rfl, t20]; norm_num
  · show dist (D.target.pts (2 + 1)) (D.target.pts (2 + 2)) = _
    rw [show ((2 : Fin 3) + 1) = 0 from rfl, show ((2 : Fin 3) + 2) = 1 from rfl, t01]; norm_num
  · rw [rot0]
    show dist (D.model.pts (2 + 1)) (D.model.pts (2 + 2)) = _
    rw [show ((2 : Fin 3) + 1) = 0 from rfl, show ((2 : Fin 3) + 2) = 1 from rfl, m01]; norm_num
  · rw [rot1]
    show dist (D.model.pts (0 + 1)) (D.model.pts (0 + 2)) = _
    rw [show ((0 : Fin 3) + 1) = 1 from rfl, show ((0 : Fin 3) + 2) = 2 from rfl, m12]; norm_num
  · rw [rot2]
    show dist (D.model.pts (1 + 1)) (D.model.pts (1 + 2)) = _
    rw [show ((1 : Fin 3) + 1) = 2 from rfl, show ((1 : Fin 3) + 2) = 0 from rfl, m20]; norm_num

end Erdos634.Draft.S5N320

#print axioms Erdos634.Draft.S5N320.s5_8_2_3_tiling
#print axioms Erdos634.Draft.S5N320.not_S5Inst_8_2_3
