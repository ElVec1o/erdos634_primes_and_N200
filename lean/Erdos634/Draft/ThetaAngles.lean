/-
Draft/ThetaAngles.lean  In `AllThreshold`.  The corner-angle form of S7 is not vacuous: the converse of `SideRunGThetaMain.corners_sides_theta` and the angle witnesses.

* `cos_alpha_add_beta`: `cos (α + β) = e / (2 f)` for `α = modelAlpha e f`, `β = modelBeta e f` (`β = 3 (α + β) − π`, so `cos β = 3 c − 4 c³` for `c = cos (α + β)`; the cubic `3 x − 4 x³` is injective on `[0, 1/2]`; `c ∈ (0, 1/2)`).
* `theta_corner_angles`: the triangle with sides `|BA| = |AQ| = s f b`, `|QB| = s e b` (`s > 0`, `b = f² − e²`) has the corner angles `α + β` at `Q` and at `B` (the cosine rule: `cos = |QB| / (2 |AQ|) = e / (2 f)`).  With `corners_sides_theta` the two forms of S7 are equivalent.
* `angles_witness_4_1_2`, `angles_witness_8_2_3`: the kernel-checked tilings of `θ_4(1,2)` and `θ_8(2,3)` satisfy every hypothesis of `thm_side_theta_angles` (and the conclusion holds there: `f³ ≤ |QB|`: `8 ≤ 12` and `27 ≤ 80`).

No sorry, no native_decide.
-/
import Erdos634.Draft.ThetaWitness

open scoped Classical

namespace Erdos634.Draft.ThetaAngles

open Erdos634.Geometry Erdos634.BaseBetaTargetCoord Erdos634.Draft.SideRunG
open Erdos634.Draft.FDBBaseBetaE1 (HasSides)
open Erdos634.Draft.UniformThreshold (hasSides_congr)
open Erdos634.Draft.ThetaWitness (theta_4_1_2 theta_8_2_3)

variable {N : ℕ}

/-- **`cos (α + β) = e / (2 f)`** -/
theorem cos_alpha_add_beta {e f : ℝ} (he : 0 < e) (hef : e < f) :
    Real.cos (modelAlpha e f + modelBeta e f) = e / (2 * f) := by
  have hf : 0 < f := he.trans hef
  obtain ⟨hb0, hb2⟩ := modelBeta_mem he hef
  have hrel := modelAngle_rel e f
  have hcosb := cos_modelBeta he hef
  have hpi := Real.pi_pos
  set θ := modelAlpha e f + modelBeta e f with hθ
  have hβ : modelBeta e f = 3 * θ - Real.pi := by rw [hθ]; linarith
  have hθ1 : Real.pi / 3 < θ := by rw [hθ]; linarith
  have hθ2 : θ < Real.pi / 2 := by rw [hθ]; linarith
  have hcpos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith, hθ2⟩
  have hclt : Real.cos θ < 1 / 2 := by
    have := Real.cos_lt_cos_of_nonneg_of_le_pi (x := Real.pi / 3) (y := θ) (by linarith) (by linarith) hθ1
    rwa [Real.cos_pi_div_three] at this
  have h3 : Real.cos (modelBeta e f) = 3 * Real.cos θ - 4 * Real.cos θ ^ 3 := by
    rw [hβ, Real.cos_sub_pi, Real.cos_three_mul]; ring
  set c0 : ℝ := e / (2 * f) with hc0def
  have hc0pos : 0 < c0 := by positivity
  have hc0lt : c0 < 1 / 2 := by
    rw [hc0def, div_lt_iff₀ (by positivity)]; linarith
  have hc0 : 3 * c0 - 4 * c0 ^ 3 = baseLen e f / (2 * f ^ 3) := by
    rw [hc0def]; unfold baseLen Nq; field_simp; ring
  have key : (Real.cos θ - c0) * (3 - 4 * (Real.cos θ ^ 2 + Real.cos θ * c0 + c0 ^ 2)) = 0 := by
    linear_combination (-1 : ℝ) * h3 + hcosb - hc0
  have hpos : 0 < 3 - 4 * (Real.cos θ ^ 2 + Real.cos θ * c0 + c0 ^ 2) := by nlinarith
  have := (mul_eq_zero.mp key).resolve_right hpos.ne'
  linarith

/-- **The triangle with sides `|BA| = |AQ| = s f b`, `|QB| = s e b` has the corner angles `α + β` at `Q` and at `B`.** -/
theorem theta_corner_angles (e f : ℕ) (he : 1 ≤ e) (hef : e < f) {s : ℝ} (hs : 0 < s) (T : Erdos634.Geometry.Tri)
    (τ : Equiv.Perm (Fin 3))
    (h1 : dist (T.pts (τ 1)) (T.pts (τ 2)) = s * ((f : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)))
    (h2 : dist (T.pts (τ 2)) (T.pts (τ 0)) = s * ((f : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)))
    (h3 : dist (T.pts (τ 0)) (T.pts (τ 1)) = s * ((e : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2))) :
    cornerAngle (T.pts (τ 2)) (T.pts (τ 0)) (T.pts (τ 1)) = modelAlpha (e : ℝ) (f : ℝ) + modelBeta (e : ℝ) (f : ℝ) ∧
    cornerAngle (T.pts (τ 0)) (T.pts (τ 1)) (T.pts (τ 2)) = modelAlpha (e : ℝ) (f : ℝ) + modelBeta (e : ℝ) (f : ℝ) := by
  have he0 : (0 : ℝ) < e := Nat.cast_pos.mpr (by omega)
  have hefR : (e : ℝ) < f := by exact_mod_cast hef
  have hf0 : (0 : ℝ) < f := he0.trans hefR
  have hb := b_posG he0 hefR
  obtain ⟨hb0, hb2⟩ := modelBeta_mem he0 hefR
  have hrel := modelAngle_rel (e : ℝ) (f : ℝ)
  have hα0 : 0 < modelAlpha (e : ℝ) (f : ℝ) := by unfold modelAlpha; linarith [Real.pi_pos]
  have hcos := cos_alpha_add_beta he0 hefR
  have hleg : 0 < s * ((f : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)) := mul_pos hs (mul_pos hf0 hb)
  have hbase : 0 < s * ((e : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)) := mul_pos hs (mul_pos he0 hb)
  have hθ0 : 0 ≤ modelAlpha (e : ℝ) (f : ℝ) + modelBeta (e : ℝ) (f : ℝ) := by linarith
  have hθπ : modelAlpha (e : ℝ) (f : ℝ) + modelBeta (e : ℝ) (f : ℝ) ≤ Real.pi := by linarith [Real.pi_pos]
  refine ⟨?_, ?_⟩
  · refine cornerAngle_eq_of_cosG (a := s * ((f : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)))
      (b := s * ((e : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2))) (d := s * ((f : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)))
      h2 (by rw [dist_comm]; exact h3) (by rw [dist_comm]; exact h1) hleg hbase hθ0 hθπ ?_
    rw [hcos]; field_simp; ring
  · refine cornerAngle_eq_of_cosG (a := s * ((e : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)))
      (b := s * ((f : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2))) (d := s * ((f : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)))
      h3 (by rw [dist_comm]; exact h1) (by rw [dist_comm]; exact h2) hbase hleg hθ0 hθπ ?_
    rw [hcos]; field_simp; ring

/-- the corner-angle hypotheses of `thm_side_theta_angles` hold for the 48-tile tiling of `θ_4(1,2)`, and `f³ ≤ |QB|` there -/
theorem angles_witness_4_1_2 :
    ∃ (N : ℕ) (D₀ : CongruentDissection N) (τ : Equiv.Perm (Fin 3)),
      HasSides D₀.model ((1 : ℕ) * (2 : ℕ)) (((2 : ℕ) : ℝ) ^ 2 - ((1 : ℕ) : ℝ) ^ 2) (((2 : ℕ) : ℝ) ^ 2) ∧
      cornerAngle (D₀.target.pts (τ 2)) (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) =
        modelAlpha ((1 : ℕ) : ℝ) ((2 : ℕ) : ℝ) + modelBeta ((1 : ℕ) : ℝ) ((2 : ℕ) : ℝ) ∧
      cornerAngle (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) (D₀.target.pts (τ 2)) =
        modelAlpha ((1 : ℕ) : ℝ) ((2 : ℕ) : ℝ) + modelBeta ((1 : ℕ) : ℝ) ((2 : ℕ) : ℝ) ∧
      ((2 : ℕ) : ℝ) ^ 3 ≤ dist (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) := by
  obtain ⟨N, D, hT, hM⟩ := theta_4_1_2
  obtain ⟨τ, h1, h2, h3⟩ := hT
  have hM' : HasSides D.model ((1 : ℕ) * (2 : ℕ)) (((2 : ℕ) : ℝ) ^ 2 - ((1 : ℕ) : ℝ) ^ 2) (((2 : ℕ) : ℝ) ^ 2) :=
    hasSides_congr hM (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨hQ, hB⟩ := theta_corner_angles 1 2 le_rfl (by norm_num) (s := 4) (by norm_num) D.target τ
    (by rw [h1]; norm_num) (by rw [h2]; norm_num) (by rw [h3]; norm_num)
  refine ⟨N, D, τ, hM', hQ, hB, ?_⟩
  rw [h3]; norm_num

/-- the corner-angle hypotheses of `thm_side_theta_angles` hold for the 320-tile tiling of `θ_8(2,3)` -/
theorem angles_witness_8_2_3 :
    ∃ (N : ℕ) (D₀ : CongruentDissection N) (τ : Equiv.Perm (Fin 3)),
      HasSides D₀.model ((2 : ℕ) * (3 : ℕ)) (((3 : ℕ) : ℝ) ^ 2 - ((2 : ℕ) : ℝ) ^ 2) (((3 : ℕ) : ℝ) ^ 2) ∧
      cornerAngle (D₀.target.pts (τ 2)) (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) =
        modelAlpha ((2 : ℕ) : ℝ) ((3 : ℕ) : ℝ) + modelBeta ((2 : ℕ) : ℝ) ((3 : ℕ) : ℝ) ∧
      cornerAngle (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) (D₀.target.pts (τ 2)) =
        modelAlpha ((2 : ℕ) : ℝ) ((3 : ℕ) : ℝ) + modelBeta ((2 : ℕ) : ℝ) ((3 : ℕ) : ℝ) ∧
      ((3 : ℕ) : ℝ) ^ 3 ≤ dist (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) := by
  obtain ⟨N, D, hT, hM⟩ := theta_8_2_3
  obtain ⟨τ, h1, h2, h3⟩ := hT
  have hM' : HasSides D.model ((2 : ℕ) * (3 : ℕ)) (((3 : ℕ) : ℝ) ^ 2 - ((2 : ℕ) : ℝ) ^ 2) (((3 : ℕ) : ℝ) ^ 2) :=
    hasSides_congr hM (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨hQ, hB⟩ := theta_corner_angles 2 3 (by norm_num) (by norm_num) (s := 8) (by norm_num) D.target τ
    (by rw [h1]; norm_num) (by rw [h2]; norm_num) (by rw [h3]; norm_num)
  refine ⟨N, D, τ, hM', hQ, hB, ?_⟩
  rw [h3]; norm_num

end Erdos634.Draft.ThetaAngles

#print axioms Erdos634.Draft.ThetaAngles.cos_alpha_add_beta
#print axioms Erdos634.Draft.ThetaAngles.theta_corner_angles
#print axioms Erdos634.Draft.ThetaAngles.angles_witness_4_1_2
#print axioms Erdos634.Draft.ThetaAngles.angles_witness_8_2_3
