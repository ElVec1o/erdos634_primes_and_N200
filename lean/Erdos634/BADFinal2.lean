import Erdos634.BADFinal

/-!
# BAD layer L2, final form of `prop:basealphadiv` (`BAD.theoremA_L2_full`)  Hypotheses: a `CongruentDissection` whose model has side lengths
`(ef, f²-e², f²)` (`gcd(e,f)=1`, `0<e<f`) and whose target is a triangle with two equal sides `X`
opposite two vertices carrying the model's angle `α` (opposite `ef`) and third side `Y` (any vertex
labelling).  Conclusion (as in the paper): `X = f² w`, `Y = (2f²-e²) w` with `w ∈ ℤ` and `(f²-e²) ∣ w`.
-/

open LaurentPolynomial

namespace Erdos634.BADL2
open Erdos634.Geometry Erdos634.NormalPosition

noncomputable section

theorem cop_f2_Q {e f : ℤ} (h : IsCoprime e f) : IsCoprime (f ^ 2) (2 * f ^ 2 - e ^ 2) := by
  obtain ⟨u, v, huv⟩ := h.symm.pow (m := 2) (n := 2)
  exact ⟨u + 2 * v, -v, by linear_combination huv⟩

theorem theoremA_L2_full {N : ℕ} (D : CongruentDissection N) (e f : ℤ) (h0 : 0 < e) (hef : e < f)
    (hcop : IsCoprime e f) (X Y : ℝ)
    (σ : Equiv.Perm (Fin 3))
    (l0 : D.model.oppLen (σ 0) = (e : ℝ) * f)
    (l1 : D.model.oppLen (σ 1) = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (l2 : D.model.oppLen (σ 2) = (f : ℝ) ^ 2)
    (τ : Equiv.Perm (Fin 3))
    (a0 : D.target.angleAt (τ 0) = D.model.angleAt (σ 0))
    (a1 : D.target.angleAt (τ 1) = D.model.angleAt (σ 0))
    (m0 : D.target.oppLen (τ 0) = X) (m1 : D.target.oppLen (τ 1) = X)
    (m2 : D.target.oppLen (τ 2) = Y) :
    ∃ w : ℤ, X = (f : ℝ) ^ 2 * w ∧ Y = (2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2) * w ∧ (f ^ 2 - e ^ 2) ∣ w := by
  obtain ⟨hcα, h3, hγ, hirr⟩ := tile_angles D.model σ e f h0 hef l0 l1 l2
  generalize hαg : D.model.angleAt (σ 0) = α at hcα h3 hγ hirr a0 a1
  generalize hβg : D.model.angleAt (σ 1) = β at h3 hγ
  obtain ⟨D', hM, hO, hA⟩ : ∃ D' : CongruentDissection N, D'.model = D.model ∧
      (∀ k, D'.target.oppLen k = D.target.oppLen (τ k)) ∧
      (∀ k, D'.target.angleAt k = D.target.angleAt (τ k)) :=
    ⟨relabelCD D τ, rfl, fun k => relabel_opp _ _ _, fun k => relabel_ang _ _ _⟩
  have hf : (0 : ℝ) < f := by exact_mod_cast lt_trans h0 hef
  have hf2 : (0 : ℝ) < (f : ℝ) ^ 2 := by positivity
  have o0 : D'.target.oppLen 0 = X := by rw [hO]; exact m0
  have o1 : D'.target.oppLen 1 = X := by rw [hO]; exact m1
  have o2 : D'.target.oppLen 2 = Y := by rw [hO]; exact m2
  have hT0 : D'.target.angleAt 0 = α := by rw [hA]; exact a0
  have hT1 : D'.target.angleAt 1 = α := by rw [hA]; exact a1
  have hYpos : 0 < Y := by rw [← o2]; exact opp_pos _ 2
  have hXpos : 0 < X := by rw [← o0]; exact opp_pos _ 0
  have hm : ∃ σ : Equiv.Perm (Fin 3),
      D'.model.angleAt (σ 0) = α ∧ D'.model.oppLen (σ 0) = (e : ℝ) * f ∧
      D'.model.angleAt (σ 1) = β ∧ D'.model.oppLen (σ 1) = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 ∧
      D'.model.angleAt (σ 2) = Real.pi - α - β ∧ D'.model.oppLen (σ 2) = (f : ℝ) ^ 2 := by
    rw [hM]; exact ⟨σ, hαg, l0, hβg, l1, hγ, l2⟩
  have ht : D'.target.angleAt 0 = α ∧ D'.target.angleAt 1 = α ∧
      D'.target.oppLen 0 = X ∧ D'.target.oppLen 1 = X ∧ D'.target.oppLen 2 = Y :=
    ⟨hT0, hT1, o0, o1, o2⟩
  obtain ⟨X', Y', l, hX', hY', hBd⟩ := L2 D' e f α β hirr h3 hm X Y ht
  -- closure: `Y = 2 X cos α`
  obtain ⟨c0, -, -⟩ := cos_laws D'.target
  rw [o0, o1, o2, hT0, hcα] at c0
  have hQ : 2 * X * Y * (2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2) = Y ^ 2 * (2 * (f : ℝ) ^ 2) := by
    have h2 : 2 * X * Y * (2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
        = (2 * X * Y * ((2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2) / (2 * (f : ℝ) ^ 2))) * (2 * (f : ℝ) ^ 2) := by
      field_simp
    rw [h2, c0]; ring
  have hXQ : X * (2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2) = (f : ℝ) ^ 2 * Y := by
    apply mul_right_cancel₀ hYpos.ne'
    linear_combination hQ / 2
  have hint : X' * (2 * f ^ 2 - e ^ 2) = f ^ 2 * Y' := by
    have : (X' : ℝ) * (2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2) = (f : ℝ) ^ 2 * Y' := by
      rw [← hX', ← hY']; exact hXQ
    exact_mod_cast this
  have hdvd : f ^ 2 ∣ X' := by
    have : f ^ 2 ∣ X' * (2 * f ^ 2 - e ^ 2) := ⟨Y', by rw [hint]⟩
    exact (cop_f2_Q hcop).dvd_of_dvd_mul_right this
  obtain ⟨w, hw⟩ := hdvd
  have hf2z : (f ^ 2 : ℤ) ≠ 0 := pow_ne_zero 2 (by omega)
  have hY'w : Y' = (2 * f ^ 2 - e ^ 2) * w := by
    apply mul_left_cancel₀ hf2z
    rw [← hint, hw]; ring
  refine ⟨w, ?_, ?_, ?_⟩
  · rw [hX', hw]; push_cast; ring
  · rw [hY', hY'w]; push_cast; ring
  · exact BAD.basealpha_div_of_poly e f w h0 hef (cop_e_b hcop) (cop_f_b hcop) l
      (by rw [Bdry_eq_Bd, ← hw, ← hY'w]; exact hBd)

end

end Erdos634.BADL2

#print axioms Erdos634.BADL2.theoremA_L2_full
