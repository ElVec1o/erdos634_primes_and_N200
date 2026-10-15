import Erdos634.ATDL2
import Erdos634.BADFinal2

/-!
# Atom divisibility at the dissection level (`atomDiv_L2_full`)  Atoms need `b ∣ μ`.
Hypotheses: a `CongruentDissection` (any `N`, reflections allowed, not nec. edge-to-edge) whose model has
side lengths `(ef, f²-e², f²)` (`gcd(e,f)=1`, `0<e<f`) under a vertex labelling `σ`, and whose target is a
triangle with two equal sides `X` opposite two vertices whose angle is `α+β` (the model's angles at `σ 0`,
`σ 1`) and third side `Y`.  Conclusion: `X = f μ`, `Y = e μ`, `μ ∈ ℤ`, `(f²-e²) ∣ μ`.
Integer corollary `atom_count`: if moreover `(f²-e²) N = μ²` (the area relation, not derived here) then
`N = (f²-e²) r²`.
-/

open LaurentPolynomial

namespace Erdos634.ATDL2
open Erdos634.Geometry Erdos634.BADL2

noncomputable section

theorem atomDiv_L2_full {N : ℕ} (D : CongruentDissection N) (e f : ℤ) (h0 : 0 < e) (hef : e < f)
    (hcop : IsCoprime e f) (X Y : ℝ)
    (σ : Equiv.Perm (Fin 3))
    (l0 : D.model.oppLen (σ 0) = (e : ℝ) * f)
    (l1 : D.model.oppLen (σ 1) = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (l2 : D.model.oppLen (σ 2) = (f : ℝ) ^ 2)
    (τ : Equiv.Perm (Fin 3))
    (a0 : D.target.angleAt (τ 0) = D.model.angleAt (σ 0) + D.model.angleAt (σ 1))
    (a1 : D.target.angleAt (τ 1) = D.model.angleAt (σ 0) + D.model.angleAt (σ 1))
    (m0 : D.target.oppLen (τ 0) = X) (m1 : D.target.oppLen (τ 1) = X)
    (m2 : D.target.oppLen (τ 2) = Y) :
    ∃ μ : ℤ, X = (f : ℝ) * μ ∧ Y = (e : ℝ) * μ ∧ (f ^ 2 - e ^ 2) ∣ μ := by
  obtain ⟨hcα, h3, hγ, hirr⟩ := tile_angles D.model σ e f h0 hef l0 l1 l2
  generalize hαg : D.model.angleAt (σ 0) = α at hcα h3 hγ hirr a0 a1
  generalize hβg : D.model.angleAt (σ 1) = β at h3 hγ a0 a1
  obtain ⟨D', hM, hO, hA⟩ : ∃ D' : CongruentDissection N, D'.model = D.model ∧
      (∀ k, D'.target.oppLen k = D.target.oppLen (τ k)) ∧
      (∀ k, D'.target.angleAt k = D.target.angleAt (τ k)) :=
    ⟨relabelCD D τ, rfl, fun k => relabel_opp _ _ _, fun k => relabel_ang _ _ _⟩
  have hf : (0 : ℝ) < f := by exact_mod_cast lt_trans h0 hef
  have he : (0 : ℝ) < e := by exact_mod_cast h0
  have o0 : D'.target.oppLen 0 = X := by rw [hO]; exact m0
  have o1 : D'.target.oppLen 1 = X := by rw [hO]; exact m1
  have o2 : D'.target.oppLen 2 = Y := by rw [hO]; exact m2
  have hT0 : D'.target.angleAt 0 = α + β := by rw [hA]; exact a0
  have hT1 : D'.target.angleAt 1 = α + β := by rw [hA]; exact a1
  have hYpos : 0 < Y := by rw [← o2]; exact opp_pos _ 2
  have hXpos : 0 < X := by rw [← o0]; exact opp_pos _ 0
  have hm : ∃ σ : Equiv.Perm (Fin 3),
      D'.model.angleAt (σ 0) = α ∧ D'.model.oppLen (σ 0) = (e : ℝ) * f ∧
      D'.model.angleAt (σ 1) = β ∧ D'.model.oppLen (σ 1) = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 ∧
      D'.model.angleAt (σ 2) = Real.pi - α - β ∧ D'.model.oppLen (σ 2) = (f : ℝ) ^ 2 := by
    rw [hM]; exact ⟨σ, hαg, l0, hβg, l1, hγ, l2⟩
  have ht : D'.target.angleAt 0 = α + β ∧ D'.target.angleAt 1 = α + β ∧
      D'.target.oppLen 0 = X ∧ D'.target.oppLen 1 = X ∧ D'.target.oppLen 2 = Y :=
    ⟨hT0, hT1, o0, o1, o2⟩
  obtain ⟨X', Y', l, hX', hY', hBd⟩ := L2atom D' e f α β hirr h3 hm X Y ht
  -- closure: the apex angle is `α`, so `f² Y² = e² X²`
  have hs := D'.target.angleAt_sum
  have hap : D'.target.angleAt 2 = α := by linarith
  obtain ⟨-, -, c2⟩ := cos_laws D'.target
  rw [o0, o1, o2, hap, hcα] at c2
  have hc' : (2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2) / (2 * (f : ℝ) ^ 2) * (2 * (f : ℝ) ^ 2)
      = 2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by field_simp
  have hY2 : (f : ℝ) ^ 2 * Y ^ 2 = (e : ℝ) ^ 2 * X ^ 2 := by
    linear_combination (f : ℝ) ^ 2 * c2 - X ^ 2 * hc'
  have hYX : Y * f = e * X := by
    have hp : (0 : ℝ) < Y * f + e * X := by positivity
    have : (Y * f - e * X) * (Y * f + e * X) = 0 := by linear_combination hY2
    rcases mul_eq_zero.mp this with h | h
    · linarith
    · linarith
  have hint : Y' * f = e * X' := by
    have : (Y' : ℝ) * f = e * X' := by rw [← hX', ← hY']; exact hYX
    exact_mod_cast this
  have hdvd : f ∣ X' := by
    have : f ∣ X' * e := ⟨Y', by linear_combination -hint⟩
    first | exact hcop.symm.dvd_of_dvd_mul_right this | exact hcop.symm.dvd_of_dvd_mul_left this
  obtain ⟨μ, hμ⟩ := hdvd
  have hfz : f ≠ 0 := by omega
  have hY'μ : Y' = e * μ := by
    apply mul_right_cancel₀ hfz
    rw [hint, hμ]; ring
  refine ⟨μ, ?_, ?_, ?_⟩
  · rw [hX', hμ]; push_cast; ring
  · rw [hY', hY'μ]; push_cast; ring
  · exact ATD.atomdiv_of_poly e f μ h0 hef (cop_e_b hcop) l
      (by unfold ATD.Ba; rw [← hμ, ← hY'μ]; exact hBd)

/-- integer corollary: `(f²-e²) ∣ μ` and the area relation `(f²-e²) N = μ²` give `N = (f²-e²) r²`. -/
theorem atom_count (b μ : ℤ) (N : ℕ) (hb : 0 < b) (hd : b ∣ μ) (harea : b * (N : ℤ) = μ ^ 2) :
    ∃ r : ℤ, (N : ℤ) = b * r ^ 2 := by
  obtain ⟨r, hr⟩ := hd
  refine ⟨r, ?_⟩
  apply mul_left_cancel₀ hb.ne'
  rw [harea, hr]; ring

end

end Erdos634.ATDL2

#print axioms Erdos634.ATDL2.atomDiv_L2_full
#print axioms Erdos634.ATDL2.atom_count
