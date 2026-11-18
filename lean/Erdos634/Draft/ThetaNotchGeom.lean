-- Draft/ThetaNotchGeom.lean -- SSS helper for the six side permutations, the model tile, target-triangle membership.
-- INTERNAL BUILD ONLY, UNAUDITED.  No sorry, no native_decide.
/-
Credit: Paliy, Beeson, Laczkovich, Zhang, Beeson-Rosu; the project (`ThetaUnit*`, `LadderFam`, `SssCongruent`).
INTERNAL BUILD ONLY, UNAUDITED.
-/
import Erdos634.Draft.ThetaNotchFrame

open scoped Classical
open Erdos634.Geometry Erdos634.CertCoord

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Erdos634.Draft.ThetaNotch
noncomputable section
open Erdos634.Draft.WFrameF Erdos634.Draft.RegionTiling Erdos634.Draft.WBrickF Erdos634.Draft.CollarLayer
open Erdos634.Draft.LadderFam Erdos634.Draft.CollarFam
open Erdos634.Draft.S2L (baseTri tri_eq_of_pts)

theorem cong_perm {T U : Erdos634.Geometry.Tri} (σ : Equiv.Perm (Fin 3)) (x y z : ℝ)
    (hT01 : dist (T.pts 0) (T.pts 1) ^ 2 = x) (hT12 : dist (T.pts 1) (T.pts 2) ^ 2 = y)
    (hT02 : dist (T.pts 0) (T.pts 2) ^ 2 = z)
    (hU01 : dist (U.pts (σ 0)) (U.pts (σ 1)) ^ 2 = x) (hU12 : dist (U.pts (σ 1)) (U.pts (σ 2)) ^ 2 = y)
    (hU02 : dist (U.pts (σ 0)) (U.pts (σ 2)) ^ 2 = z) : T.Congruent U := by
  have hT10 : dist (T.pts 1) (T.pts 0) ^ 2 = x := by rw [dist_comm]; exact hT01
  have hT21 : dist (T.pts 2) (T.pts 1) ^ 2 = y := by rw [dist_comm]; exact hT12
  have hT20 : dist (T.pts 2) (T.pts 0) ^ 2 = z := by rw [dist_comm]; exact hT02
  have hU10 : dist (U.pts (σ 1)) (U.pts (σ 0)) ^ 2 = x := by rw [dist_comm]; exact hU01
  have hU21 : dist (U.pts (σ 2)) (U.pts (σ 1)) ^ 2 = y := by rw [dist_comm]; exact hU12
  have hU20 : dist (U.pts (σ 2)) (U.pts (σ 0)) ^ 2 = z := by rw [dist_comm]; exact hU02
  refine Erdos634.SssCongruent.congruent_of_sq_dist_perm σ ?_
  intro i j
  fin_cases i <;> fin_cases j <;> simp [hT01, hT12, hT02, hT10, hT21, hT20, hU01, hU12, hU02, hU10, hU21, hU20]

/-- SSS from the three squared side lengths, in any of the six assignments -/
theorem cong_of_sq_triple {T U : Erdos634.Geometry.Tri} (x y z u v w : ℝ)
    (hT01 : dist (T.pts 0) (T.pts 1) ^ 2 = x) (hT12 : dist (T.pts 1) (T.pts 2) ^ 2 = y)
    (hT02 : dist (T.pts 0) (T.pts 2) ^ 2 = z)
    (hU01 : dist (U.pts 0) (U.pts 1) ^ 2 = u) (hU12 : dist (U.pts 1) (U.pts 2) ^ 2 = v)
    (hU02 : dist (U.pts 0) (U.pts 2) ^ 2 = w)
    (hp : (x = u ∧ y = v ∧ z = w) ∨ (x = u ∧ y = w ∧ z = v) ∨ (x = v ∧ y = u ∧ z = w) ∨
      (x = v ∧ y = w ∧ z = u) ∨ (x = w ∧ y = u ∧ z = v) ∨ (x = w ∧ y = v ∧ z = u)) :
    T.Congruent U := by
  have hU10 : dist (U.pts 1) (U.pts 0) ^ 2 = u := by rw [dist_comm]; exact hU01
  have hU21 : dist (U.pts 2) (U.pts 1) ^ 2 = v := by rw [dist_comm]; exact hU12
  have hU20 : dist (U.pts 2) (U.pts 0) ^ 2 = w := by rw [dist_comm]; exact hU02
  rcases hp with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · exact cong_perm (Equiv.refl _) x y z hT01 hT12 hT02 (by simp [h1, hU01, hU10, hU12, hU21, hU02, hU20, Equiv.swap_apply_def, Equiv.trans_apply]) (by simp [h2, hU01, hU10, hU12, hU21, hU02, hU20, Equiv.swap_apply_def, Equiv.trans_apply]) (by simp [h3, hU01, hU10, hU12, hU21, hU02, hU20, Equiv.swap_apply_def, Equiv.trans_apply])
  · exact cong_perm (Equiv.swap 0 1) x y z hT01 hT12 hT02 (by simp [h1, hU01, hU10, hU12, hU21, hU02, hU20, Equiv.swap_apply_def, Equiv.trans_apply]) (by simp [h2, hU01, hU10, hU12, hU21, hU02, hU20, Equiv.swap_apply_def, Equiv.trans_apply]) (by simp [h3, hU01, hU10, hU12, hU21, hU02, hU20, Equiv.swap_apply_def, Equiv.trans_apply])
  · exact cong_perm (Equiv.swap 0 2) x y z hT01 hT12 hT02 (by simp [h1, hU01, hU10, hU12, hU21, hU02, hU20, Equiv.swap_apply_def, Equiv.trans_apply]) (by simp [h2, hU01, hU10, hU12, hU21, hU02, hU20, Equiv.swap_apply_def, Equiv.trans_apply]) (by simp [h3, hU01, hU10, hU12, hU21, hU02, hU20, Equiv.swap_apply_def, Equiv.trans_apply])
  · exact cong_perm ((Equiv.swap 0 1).trans (Equiv.swap 0 2)) x y z hT01 hT12 hT02 (by simp [h1, hU01, hU10, hU12, hU21, hU02, hU20, Equiv.swap_apply_def, Equiv.trans_apply]) (by simp [h2, hU01, hU10, hU12, hU21, hU02, hU20, Equiv.swap_apply_def, Equiv.trans_apply]) (by simp [h3, hU01, hU10, hU12, hU21, hU02, hU20, Equiv.swap_apply_def, Equiv.trans_apply])
  · exact cong_perm ((Equiv.swap 0 2).trans (Equiv.swap 0 1)) x y z hT01 hT12 hT02 (by simp [h1, hU01, hU10, hU12, hU21, hU02, hU20, Equiv.swap_apply_def, Equiv.trans_apply]) (by simp [h2, hU01, hU10, hU12, hU21, hU02, hU20, Equiv.swap_apply_def, Equiv.trans_apply]) (by simp [h3, hU01, hU10, hU12, hU21, hU02, hU20, Equiv.swap_apply_def, Equiv.trans_apply])
  · exact cong_perm (Equiv.swap 1 2) x y z hT01 hT12 hT02 (by simp [h1, hU01, hU10, hU12, hU21, hU02, hU20, Equiv.swap_apply_def, Equiv.trans_apply]) (by simp [h2, hU01, hU10, hU12, hU21, hU02, hU20, Equiv.swap_apply_def, Equiv.trans_apply]) (by simp [h3, hU01, hU10, hU12, hU21, hU02, hU20, Equiv.swap_apply_def, Equiv.trans_apply])

/-- squared real length of an apex vector pair -/
def qf (E F : ℝ) (p q : ℝ × ℝ) : ℝ :=
  (F ^ 2 - E ^ 2) ^ 2 * (F ^ 2 * ((p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2) + (2 * F ^ 2 - E ^ 2) * ((p.1 - q.1) * (p.2 - q.2)))

section model
variable {φ : ℝ} (hφ : 1 < φ) (e f : ℕ) (he : 0 < e) (hef : e < f) (hφE : φ = (f : ℝ) / e)
include hφE

theorem mrow_d01 : dist ((Mrow hφ e f he hef).pts 0) ((Mrow hφ e f he hef).pts 1) ^ 2 = (((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ^ 2) := by
  simp only [Mrow, brickL, triC_pts, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  rw [sq_Phi hφ]; simp; ring

theorem mrow_d12 : dist ((Mrow hφ e f he hef).pts 1) ((Mrow hφ e f he hef).pts 2) ^ 2 = (((e : ℝ) * f) ^ 2) := by
  simp only [Mrow, brickL, triC_pts, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  rw [sq_Phi hφ]; simp

theorem mrow_d02 : dist ((Mrow hφ e f he hef).pts 0) ((Mrow hφ e f he hef).pts 2) ^ 2 = (((f : ℝ) ^ 2) ^ 2) := by
  have hE : (0 : ℝ) < e := by exact_mod_cast he
  have hF : (0 : ℝ) < f := by have : (e : ℝ) < f := by exact_mod_cast hef
                              linarith
  simp only [Mrow, brickL, triC_pts, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  rw [sq_Phi hφ]; subst hφE; simp; field_simp; ring

end model

section apexcong
variable {φ : ℝ} (hφ : 1 < φ) (e f : ℕ) (he : 0 < e) (hef : e < f) (hφE : φ = (f : ℝ) / e) (s : ℝ)
include hφE

/-- the three squared side lengths of the model, as the target of `cong_of_sq_triple` -/
theorem cong_apex3 (a b c : ℝ × ℝ) (h) (x y z : ℝ)
    (hx : qf (e : ℝ) f a b = x) (hy : qf (e : ℝ) f b c = y) (hz : qf (e : ℝ) f a c = z)
    (hp : (x = (((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ^ 2) ∧ y = (((e : ℝ) * f) ^ 2) ∧ z = (((f : ℝ) ^ 2) ^ 2)) ∨
      (x = (((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ^ 2) ∧ y = (((f : ℝ) ^ 2) ^ 2) ∧ z = (((e : ℝ) * f) ^ 2)) ∨
      (x = (((e : ℝ) * f) ^ 2) ∧ y = (((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ^ 2) ∧ z = (((f : ℝ) ^ 2) ^ 2)) ∨
      (x = (((e : ℝ) * f) ^ 2) ∧ y = (((f : ℝ) ^ 2) ^ 2) ∧ z = (((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ^ 2)) ∨
      (x = (((f : ℝ) ^ 2) ^ 2) ∧ y = (((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ^ 2) ∧ z = (((e : ℝ) * f) ^ 2)) ∨
      (x = (((f : ℝ) ^ 2) ^ 2) ∧ y = (((e : ℝ) * f) ^ 2) ∧ z = (((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ^ 2))) :
    (triC φ hφ (cH (e : ℝ) f s a) (cH (e : ℝ) f s b) (cH (e : ℝ) f s c) h).Congruent (Mrow hφ e f he hef) := by
  have hE : (0 : ℝ) < e := by exact_mod_cast he
  have hEF : (e : ℝ) < f := by exact_mod_cast hef
  refine cong_of_sq_triple x y z _ _ _ ?_ ?_ ?_ (mrow_d01 hφ e f he hef hφE) (mrow_d12 hφ e f he hef hφE) (mrow_d02 hφ e f he hef hφE) hp
  · simp only [triC_pts, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
    rw [dist2_cH s hE hEF hφ hφE]; exact hx
  · simp only [triC_pts, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
    rw [dist2_cH s hE hEF hφ hφE]; exact hy
  · simp only [triC_pts, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
    rw [dist2_cH s hE hEF hφ hφE]; exact hz

theorem cong_apexT (T : Erdos634.Geometry.Tri) (a b c : ℝ × ℝ)
    (h0 : T.pts 0 = Phi φ (cH (e : ℝ) f s a)) (h1 : T.pts 1 = Phi φ (cH (e : ℝ) f s b)) (h2 : T.pts 2 = Phi φ (cH (e : ℝ) f s c))
    (x y z : ℝ)
    (hx : qf (e : ℝ) f a b = x) (hy : qf (e : ℝ) f b c = y) (hz : qf (e : ℝ) f a c = z)
    (hp : (x = (((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ^ 2) ∧ y = (((e : ℝ) * f) ^ 2) ∧ z = (((f : ℝ) ^ 2) ^ 2)) ∨
      (x = (((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ^ 2) ∧ y = (((f : ℝ) ^ 2) ^ 2) ∧ z = (((e : ℝ) * f) ^ 2)) ∨
      (x = (((e : ℝ) * f) ^ 2) ∧ y = (((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ^ 2) ∧ z = (((f : ℝ) ^ 2) ^ 2)) ∨
      (x = (((e : ℝ) * f) ^ 2) ∧ y = (((f : ℝ) ^ 2) ^ 2) ∧ z = (((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ^ 2)) ∨
      (x = (((f : ℝ) ^ 2) ^ 2) ∧ y = (((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ^ 2) ∧ z = (((e : ℝ) * f) ^ 2)) ∨
      (x = (((f : ℝ) ^ 2) ^ 2) ∧ y = (((e : ℝ) * f) ^ 2) ∧ z = (((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ^ 2))) :
    T.Congruent (Mrow hφ e f he hef) := by
  have hE : (0 : ℝ) < e := by exact_mod_cast he
  have hEF : (e : ℝ) < f := by exact_mod_cast hef
  refine cong_of_sq_triple x y z _ _ _ ?_ ?_ ?_ (mrow_d01 hφ e f he hef hφE) (mrow_d12 hφ e f he hef hφE) (mrow_d02 hφ e f he hef hφE) hp
  · rw [h0, h1, dist2_cH s hE hEF hφ hφE]; exact hx
  · rw [h1, h2, dist2_cH s hE hEF hφ hφE]; exact hy
  · rw [h0, h2, dist2_cH s hE hEF hφ hφE]; exact hz

end apexcong

end

end Erdos634.Draft.ThetaNotch
