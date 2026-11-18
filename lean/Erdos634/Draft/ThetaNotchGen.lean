-- Draft/ThetaNotchGen.lean -- generic apex-frame lemmas: determinants, base-tile congruence of apex triangles, target membership.
-- INTERNAL BUILD ONLY, UNAUDITED.  No sorry, no native_decide.
/-
Credit: Paliy, Beeson, Laczkovich, Zhang, Beeson-Rosu; the project (`ThetaUnit*`, `LadderFam`).  INTERNAL BUILD ONLY, UNAUDITED.
-/
import Erdos634.Draft.ThetaNotchGeom

open scoped Classical
open Erdos634.Geometry Erdos634.CertCoord

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Erdos634.Draft.ThetaNotch
noncomputable section
open Erdos634.Draft.WFrameF Erdos634.Draft.RegionTiling Erdos634.Draft.WBrickF Erdos634.Draft.CollarLayer
open Erdos634.Draft.LadderFam Erdos634.Draft.CollarFam
open Erdos634.Draft.S2L (baseTri tri_eq_of_pts)

section gen
variable {E F : ℝ} (s : ℝ) (hE : 0 < E) (hEF : E < F)
include hE hEF

theorem cH_seg (a b : ℝ × ℝ) (α : ℝ) :
    cH E F s (a + α • (b - a)) = cH E F s a + α • (cH E F s b - cH E F s a) := by
  ext <;> simp only [cH, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, Prod.fst_sub, Prod.snd_sub] <;> ring

/-- determinant in the skew frame of an apex triple -/
theorem det_cH (a V1 V2 : ℝ × ℝ) :
    ((cH E F s V1).1 - (cH E F s a).1) * ((cH E F s V2).2 - (cH E F s a).2) -
      ((cH E F s V2).1 - (cH E F s a).1) * ((cH E F s V1).2 - (cH E F s a).2) =
    F * E * (F ^ 2 - E ^ 2) ^ 2 * ((V1.1 - a.1) * (V2.2 - a.2) - (V2.1 - a.1) * (V1.2 - a.2)) := by
  simp only [cH]; ring

theorem det_cH_ne (a V1 V2 : ℝ × ℝ) (h : (V1.1 - a.1) * (V2.2 - a.2) - (V2.1 - a.1) * (V1.2 - a.2) ≠ 0) :
    ((cH E F s V1).1 - (cH E F s a).1) * ((cH E F s V2).2 - (cH E F s a).2) -
      ((cH E F s V2).1 - (cH E F s a).1) * ((cH E F s V1).2 - (cH E F s a).2) ≠ 0 := by
  obtain ⟨hF, hb⟩ := frame_pos hE hEF
  rw [det_cH s hE hEF]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero hF.ne' hE.ne') (pow_ne_zero 2 hb.ne')) h

theorem qf_seg (a V : ℝ × ℝ) (k : ℝ) (hk : k ≠ 0) :
    qf E F a (a + (1 / k) • (V - a)) = qf E F a V / k ^ 2 := by
  simp only [qf, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, Prod.fst_sub, Prod.snd_sub]
  field_simp; ring

theorem qf_seg2 (a V1 V2 : ℝ × ℝ) (k : ℝ) (hk : k ≠ 0) :
    qf E F (a + (1 / k) • (V1 - a)) (a + (1 / k) • (V2 - a)) = qf E F V1 V2 / k ^ 2 := by
  simp only [qf, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, Prod.fst_sub, Prod.snd_sub]
  field_simp; ring

end gen

section basecong
variable {φ : ℝ} (hφ : 1 < φ) (e f : ℕ) (he : 0 < e) (hef : e < f) (hφE : φ = (f : ℝ) / e) (s : ℝ)
include hφE

/-- the base tile of the apex triangle `a, V1, V2` of scale `k` is congruent to the model, from the big side lengths -/
theorem cong_base_apex (a V1 V2 : ℝ × ℝ) (k : ℕ) (hk : 0 < k) (h) (x y z : ℝ)
    (hx : qf (e : ℝ) f a V1 = (k : ℝ) ^ 2 * x) (hy : qf (e : ℝ) f V1 V2 = (k : ℝ) ^ 2 * y)
    (hz : qf (e : ℝ) f a V2 = (k : ℝ) ^ 2 * z)
    (hp : (x = (((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ^ 2) ∧ y = (((e : ℝ) * f) ^ 2) ∧ z = (((f : ℝ) ^ 2) ^ 2)) ∨
      (x = (((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ^ 2) ∧ y = (((f : ℝ) ^ 2) ^ 2) ∧ z = (((e : ℝ) * f) ^ 2)) ∨
      (x = (((e : ℝ) * f) ^ 2) ∧ y = (((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ^ 2) ∧ z = (((f : ℝ) ^ 2) ^ 2)) ∨
      (x = (((e : ℝ) * f) ^ 2) ∧ y = (((f : ℝ) ^ 2) ^ 2) ∧ z = (((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ^ 2)) ∨
      (x = (((f : ℝ) ^ 2) ^ 2) ∧ y = (((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ^ 2) ∧ z = (((e : ℝ) * f) ^ 2)) ∨
      (x = (((f : ℝ) ^ 2) ^ 2) ∧ y = (((e : ℝ) * f) ^ 2) ∧ z = (((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ^ 2))) :
    (baseTri φ hφ (cH (e : ℝ) f s a) (cH (e : ℝ) f s V1) (cH (e : ℝ) f s V2) k hk h).Congruent (Mrow hφ e f he hef) := by
  have hE : (0 : ℝ) < e := by exact_mod_cast he
  have hEF : (e : ℝ) < f := by exact_mod_cast hef
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  refine cong_apexT hφ e f he hef hφE s _ a (a + (1 / (k : ℝ)) • (V1 - a)) (a + (1 / (k : ℝ)) • (V2 - a)) ?_ ?_ ?_ x y z ?_ ?_ ?_ hp
  · simp only [baseTri, triC_pts, Matrix.cons_val_zero]
  · simp only [baseTri, triC_pts, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero]
    rw [cH_seg s hE hEF]
  · simp only [baseTri, triC_pts, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, Matrix.cons_val_zero]
    rw [cH_seg s hE hEF]
  · rw [qf_seg hE hEF _ _ _ hk0, hx]; field_simp
  · rw [qf_seg2 hE hEF _ _ _ _ hk0, hy]; field_simp
  · rw [qf_seg hE hEF _ _ _ hk0, hz]; field_simp

/-- the lattice cell `a, a + cHv w1, a + cHv w2` -/
theorem cong_cell_apex (a w1 w2 : ℝ × ℝ) (h) (x y z : ℝ)
    (hx : qf (e : ℝ) f a (a + w1) = x) (hy : qf (e : ℝ) f (a + w1) (a + w2) = y) (hz : qf (e : ℝ) f a (a + w2) = z)
    (hp : (x = (((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ^ 2) ∧ y = (((e : ℝ) * f) ^ 2) ∧ z = (((f : ℝ) ^ 2) ^ 2)) ∨
      (x = (((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ^ 2) ∧ y = (((f : ℝ) ^ 2) ^ 2) ∧ z = (((e : ℝ) * f) ^ 2)) ∨
      (x = (((e : ℝ) * f) ^ 2) ∧ y = (((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ^ 2) ∧ z = (((f : ℝ) ^ 2) ^ 2)) ∨
      (x = (((e : ℝ) * f) ^ 2) ∧ y = (((f : ℝ) ^ 2) ^ 2) ∧ z = (((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ^ 2)) ∨
      (x = (((f : ℝ) ^ 2) ^ 2) ∧ y = (((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ^ 2) ∧ z = (((e : ℝ) * f) ^ 2)) ∨
      (x = (((f : ℝ) ^ 2) ^ 2) ∧ y = (((e : ℝ) * f) ^ 2) ∧ z = (((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ^ 2))) :
    (triC φ hφ (cH (e : ℝ) f s a) (cH (e : ℝ) f s a + cHv (e : ℝ) f w1) (cH (e : ℝ) f s a + cHv (e : ℝ) f w2) h).Congruent
      (Mrow hφ e f he hef) := by
  have hE : (0 : ℝ) < e := by exact_mod_cast he
  have hEF : (e : ℝ) < f := by exact_mod_cast hef
  refine cong_apexT hφ e f he hef hφE s _ a (a + w1) (a + w2) ?_ ?_ ?_ x y z hx hy hz hp
  · simp only [triC_pts, Matrix.cons_val_zero]
  · simp only [triC_pts, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero]
    rw [cH_add s hE hEF]
  · simp only [triC_pts, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, Matrix.cons_val_zero]
    rw [cH_add s hE hEF]

end basecong

end

end Erdos634.Draft.ThetaNotch
