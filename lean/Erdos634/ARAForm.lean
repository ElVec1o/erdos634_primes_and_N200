import Erdos634.ARAGeom
import Erdos634.ATDFinal

/-!
# ARA: integer-level corollaries of Theorem A and of atom divisibility, area relation DERIVED  `theoremA_N_form_full`: same hypotheses as `BADL2.theoremA_L2_full`;
conclusion `N = r² (f²-e²)(2f²-e²)`.  `atomDiv_N_form_full`: same hypotheses as
`ATDL2.atomDiv_L2_full`; conclusion `N = (f²-e²) r²`.  The area relation is no longer a
hypothesis: it comes from `CongruentArea.congruentDissection_volume_target` via `ARA.area_heron`.
-/

namespace Erdos634.ARA
open Erdos634.Geometry

noncomputable section

theorem model_heron {N : ℕ} (D : CongruentDissection N) (e f : ℤ) (σ : Equiv.Perm (Fin 3))
    (l0 : D.model.oppLen (σ 0) = (e : ℝ) * f)
    (l1 : D.model.oppLen (σ 1) = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (l2 : D.model.oppLen (σ 2) = (f : ℝ) ^ 2) :
    Hh (D.model.oppLen 0) (D.model.oppLen 1) (D.model.oppLen 2) =
      (e : ℝ) ^ 2 * (4 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ^ 2 := by
  rw [← Hh_perm D.model σ, l0, l1, l2]; unfold Hh; ring

theorem target_heron {N : ℕ} (D : CongruentDissection N) (τ : Equiv.Perm (Fin 3)) (X Y : ℝ)
    (m0 : D.target.oppLen (τ 0) = X) (m1 : D.target.oppLen (τ 1) = X)
    (m2 : D.target.oppLen (τ 2) = Y) :
    Hh (D.target.oppLen 0) (D.target.oppLen 1) (D.target.oppLen 2) = Y ^ 2 * (4 * X ^ 2 - Y ^ 2) := by
  rw [← Hh_perm D.target τ, m0, m1, m2]; unfold Hh; ring

theorem cancel_sq (E N b Q w : ℝ) (hE : E ≠ 0) (hN : 0 ≤ N) (hb : 0 ≤ b) (hQ : 0 ≤ Q)
    (h : E * (N * b) ^ 2 = E * (w ^ 2 * Q) ^ 2) : N * b = w ^ 2 * Q := by
  have h1 := mul_left_cancel₀ hE h
  exact (sq_eq_sq₀ (mul_nonneg hN hb) (mul_nonneg (sq_nonneg w) hQ)).1 h1

theorem theoremA_N_form_full {N : ℕ} (D : CongruentDissection N) (e f : ℤ) (h0 : 0 < e)
    (hef : e < f) (hcop : IsCoprime e f) (X Y : ℝ)
    (σ : Equiv.Perm (Fin 3))
    (l0 : D.model.oppLen (σ 0) = (e : ℝ) * f)
    (l1 : D.model.oppLen (σ 1) = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (l2 : D.model.oppLen (σ 2) = (f : ℝ) ^ 2)
    (τ : Equiv.Perm (Fin 3))
    (a0 : D.target.angleAt (τ 0) = D.model.angleAt (σ 0))
    (a1 : D.target.angleAt (τ 1) = D.model.angleAt (σ 0))
    (m0 : D.target.oppLen (τ 0) = X) (m1 : D.target.oppLen (τ 1) = X)
    (m2 : D.target.oppLen (τ 2) = Y) :
    ∃ r : ℤ, (N : ℤ) = r ^ 2 * (f ^ 2 - e ^ 2) * (2 * f ^ 2 - e ^ 2) := by
  obtain ⟨w, hX, hY, hd⟩ := Erdos634.BADL2.theoremA_L2_full D e f h0 hef hcop X Y σ l0 l1 l2 τ
    a0 a1 m0 m1 m2
  have ha := area_heron D
  rw [model_heron D e f σ l0 l1 l2, target_heron D τ X Y m0 m1 m2, hX, hY] at ha
  have he : (0 : ℝ) < e := by exact_mod_cast h0
  have hf : (e : ℝ) < f := by exact_mod_cast hef
  have hb : (0 : ℝ) ≤ (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by nlinarith
  have hQ : (0 : ℝ) ≤ 2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by nlinarith
  have hE : (e : ℝ) ^ 2 * (4 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2) ≠ 0 := by
    have : (0 : ℝ) < 4 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by nlinarith
    positivity
  have key := cancel_sq _ (N : ℝ) _ _ w hE (Nat.cast_nonneg N) hb hQ (by linear_combination ha)
  have hZ : (N : ℤ) * (f ^ 2 - e ^ 2) = w ^ 2 * (2 * f ^ 2 - e ^ 2) := by exact_mod_cast key
  have hb0 : (f ^ 2 - e ^ 2 : ℤ) ≠ 0 := by
    have : (0 : ℝ) < (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by nlinarith
    exact_mod_cast this.ne'
  obtain ⟨r, rfl⟩ := hd
  refine ⟨r, mul_right_cancel₀ hb0 ?_⟩
  rw [hZ]; ring

theorem atomDiv_N_form_full {N : ℕ} (D : CongruentDissection N) (e f : ℤ) (h0 : 0 < e)
    (hef : e < f) (hcop : IsCoprime e f) (X Y : ℝ)
    (σ : Equiv.Perm (Fin 3))
    (l0 : D.model.oppLen (σ 0) = (e : ℝ) * f)
    (l1 : D.model.oppLen (σ 1) = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (l2 : D.model.oppLen (σ 2) = (f : ℝ) ^ 2)
    (τ : Equiv.Perm (Fin 3))
    (a0 : D.target.angleAt (τ 0) = D.model.angleAt (σ 0) + D.model.angleAt (σ 1))
    (a1 : D.target.angleAt (τ 1) = D.model.angleAt (σ 0) + D.model.angleAt (σ 1))
    (m0 : D.target.oppLen (τ 0) = X) (m1 : D.target.oppLen (τ 1) = X)
    (m2 : D.target.oppLen (τ 2) = Y) :
    ∃ μ r : ℤ, X = (f : ℝ) * μ ∧ Y = (e : ℝ) * μ ∧ (f ^ 2 - e ^ 2) * (N : ℤ) = μ ^ 2 ∧
      (N : ℤ) = (f ^ 2 - e ^ 2) * r ^ 2 := by
  obtain ⟨μ, hX, hY, hd⟩ := Erdos634.ATDL2.atomDiv_L2_full D e f h0 hef hcop X Y σ l0 l1 l2 τ
    a0 a1 m0 m1 m2
  have ha := area_heron D
  rw [model_heron D e f σ l0 l1 l2, target_heron D τ X Y m0 m1 m2, hX, hY] at ha
  have he : (0 : ℝ) < e := by exact_mod_cast h0
  have hf : (e : ℝ) < f := by exact_mod_cast hef
  have hb : (0 : ℝ) ≤ (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by nlinarith
  have hE : (e : ℝ) ^ 2 * (4 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2) ≠ 0 := by
    have : (0 : ℝ) < 4 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by nlinarith
    positivity
  have key := cancel_sq _ (N : ℝ) _ 1 (μ : ℝ) hE (Nat.cast_nonneg N) hb (by norm_num)
    (by linear_combination ha)
  have hZ : (f ^ 2 - e ^ 2) * (N : ℤ) = μ ^ 2 := by
    have : (N : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) = (μ : ℝ) ^ 2 * 1 := key
    have h2 : ((f ^ 2 - e ^ 2 : ℤ) : ℝ) * (N : ℝ) = (μ ^ 2 : ℤ) := by push_cast; linarith
    exact_mod_cast h2
  have hb0 : (f ^ 2 - e ^ 2 : ℤ) ≠ 0 := by
    have : (0 : ℝ) < (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by nlinarith
    exact_mod_cast this.ne'
  obtain ⟨r, hr⟩ := hd
  refine ⟨μ, r, hX, hY, hZ, mul_left_cancel₀ hb0 ?_⟩
  rw [hZ, hr]; ring

end

end Erdos634.ARA

#print axioms Erdos634.ARA.theoremA_N_form_full
#print axioms Erdos634.ARA.atomDiv_N_form_full
