/-
Draft/QuadConj.lean -- the field `ℚ(√3, √K)` inside `ℝ` and its automorphism `√K ↦ −√K`, `√3 ↦ √3`.

* `exists_conj`: for a subfield `E ⊆ ℝ` and a real `x ∉ E` with `x² ∈ E` there are a subfield `K ⊇ E ∪ {x}` and a ring
  homomorphism `ψ : K → ℝ` fixing `E` with `ψ x = −x` (`IntermediateField.algHomAdjoinIntegralEquiv` over the base `E`).
* `Q3`: the subfield `{a + b√3 : a, b ∈ ℚ}`; `sqrt_not_mem_Q3`: `√K ∉ Q3` when neither `K` nor `3K` is a square.
* `exists_field_conj`: the field and the homomorphism used by the conjugate-tiling kills of the `ℤ[√K]` checker
  (`ReflS<K>/CheckC.lean`): `√3, √K ∈ K`, `ψ √3 = √3`, `ψ √K = −√K`.

Pure Mathlib.  Tool for the `π/3` equilateral leaf (composite `N`); not prime-case work.  No sorry.
-/
import Mathlib

open Polynomial

namespace Erdos634.Draft.QuadConj

/-- **A quadratic extension inside `ℝ` and its conjugation.** -/
theorem exists_conj (E : Subfield ℝ) (x : ℝ) (hx2 : x ^ 2 ∈ E) (hxE : x ∉ E) :
    ∃ (K : Subfield ℝ) (ψ : K →+* ℝ) (hEK : E ≤ K) (hxK : x ∈ K),
      ψ ⟨x, hxK⟩ = -x ∧ ∀ (e : ℝ) (he : e ∈ E), ψ ⟨e, hEK he⟩ = e := by
  set k : E := ⟨x ^ 2, hx2⟩ with hk
  set p : (↥E)[X] := X ^ 2 - C k with hp
  have hpm : p.Monic := (monic_X_pow 2).sub_of_left (by rw [degree_X_pow]; exact degree_C_le.trans_lt (by norm_num))
  have hpdeg : p.natDegree = 2 := by rw [hp, natDegree_sub_C]; simp
  have hroot0 : aeval x p = 0 := by
    simp only [hp, map_sub, map_pow, aeval_X, aeval_C]
    show x ^ 2 - x ^ 2 = 0
    ring
  have hint : IsIntegral (↥E) x := ⟨p, hpm, hroot0⟩
  have hge : 2 ≤ (minpoly (↥E) x).natDegree := by
    refine (minpoly.two_le_natDegree_iff hint).mpr ?_
    rintro ⟨e, he⟩
    exact hxE (he ▸ e.2)
  have hmin : minpoly (↥E) x = p := by
    symm
    apply Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) hpm (minpoly.dvd _ _ hroot0)
    rw [hpdeg]; exact hge
  have hroot : -x ∈ (minpoly (↥E) x).aroots ℝ := by
    rw [Polynomial.mem_aroots]
    refine ⟨minpoly.ne_zero hint, ?_⟩
    rw [hmin]
    simp only [hp, map_sub, map_pow, aeval_X, aeval_C]
    show (-x) ^ 2 - x ^ 2 = 0
    ring
  set L : IntermediateField (↥E) ℝ := IntermediateField.adjoin (↥E) {x} with hL
  set σ : L →ₐ[↥E] ℝ := (IntermediateField.algHomAdjoinIntegralEquiv (↥E) hint).symm ⟨-x, hroot⟩ with hσ
  have hσx : σ ⟨x, IntermediateField.mem_adjoin_simple_self (↥E) x⟩ = -x :=
    IntermediateField.algHomAdjoinIntegralEquiv_symm_apply_gen (↥E) hint ⟨-x, hroot⟩
  have hEL : ∀ e : ℝ, e ∈ E → e ∈ L := fun e he => L.algebraMap_mem ⟨e, he⟩
  refine ⟨L.toSubfield, σ.toRingHom, fun e he => hEL e he, IntermediateField.mem_adjoin_simple_self (↥E) x, hσx, ?_⟩
  intro e he
  exact σ.commutes ⟨e, he⟩

/-! ## `ℚ(√3)` -/

theorem sqrt3_sq : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)

theorem irr3 : Irrational (Real.sqrt 3) := by
  have h := (irrational_sqrt_natCast_iff (n := 3)).mpr (by
    rintro ⟨r, hr⟩
    have : r ≤ 2 := by nlinarith
    interval_cases r <;> omega)
  simpa using h

/-- `a + b√3 = 0` with rational `a, b` forces `a = b = 0`. -/
theorem q3_zero {a b : ℚ} (h : (a : ℝ) + b * Real.sqrt 3 = 0) : a = 0 ∧ b = 0 := by
  by_cases hb : b = 0
  · subst hb
    refine ⟨?_, rfl⟩
    have : (a : ℝ) = 0 := by simpa using h
    exact_mod_cast this
  · exfalso
    apply irr3
    refine ⟨-a / b, ?_⟩
    have hb' : (b : ℝ) ≠ 0 := by exact_mod_cast hb
    push_cast
    field_simp
    linarith

/-- the subfield `{a + b√3 : a, b ∈ ℚ}` of `ℝ` -/
noncomputable def Q3 : Subfield ℝ where
  carrier := {y | ∃ a b : ℚ, y = a + b * Real.sqrt 3}
  mul_mem' := by
    rintro _ _ ⟨a, b, rfl⟩ ⟨c, d, rfl⟩
    refine ⟨a * c + 3 * b * d, a * d + b * c, ?_⟩
    push_cast
    linear_combination ((b : ℝ) * d) * sqrt3_sq
  one_mem' := ⟨1, 0, by simp⟩
  add_mem' := by
    rintro _ _ ⟨a, b, rfl⟩ ⟨c, d, rfl⟩
    exact ⟨a + c, b + d, by push_cast; ring⟩
  zero_mem' := ⟨0, 0, by simp⟩
  neg_mem' := by
    rintro _ ⟨a, b, rfl⟩
    exact ⟨-a, -b, by push_cast; ring⟩
  inv_mem' := by
    rintro _ ⟨a, b, rfl⟩
    by_cases h0 : (a : ℝ) + b * Real.sqrt 3 = 0
    · rw [h0, inv_zero]; exact ⟨0, 0, by simp⟩
    · have hn : (a : ℝ) ^ 2 - 3 * b ^ 2 ≠ 0 := by
        intro hn
        have h1 : ((a : ℝ) + b * Real.sqrt 3) * ((a : ℝ) - b * Real.sqrt 3) = 0 := by
          linear_combination hn - ((b : ℝ) ^ 2) * sqrt3_sq
        rcases mul_eq_zero.mp h1 with h | h
        · exact h0 h
        · have h' : ((a : ℚ) : ℝ) + ((-b : ℚ) : ℝ) * Real.sqrt 3 = 0 := by push_cast; linarith
          obtain ⟨ha, hb⟩ := q3_zero h'
          have hb0 : b = 0 := by linarith
          apply h0; rw [ha, hb0]; simp
      refine ⟨a / (a ^ 2 - 3 * b ^ 2), -b / (a ^ 2 - 3 * b ^ 2), inv_eq_of_mul_eq_one_right ?_⟩
      push_cast
      have e : ((a : ℝ) + b * Real.sqrt 3) * ((a : ℝ) / ((a : ℝ) ^ 2 - 3 * (b : ℝ) ^ 2) +
          -(b : ℝ) / ((a : ℝ) ^ 2 - 3 * (b : ℝ) ^ 2) * Real.sqrt 3) =
          ((a : ℝ) ^ 2 - (b : ℝ) ^ 2 * (Real.sqrt 3 * Real.sqrt 3)) / ((a : ℝ) ^ 2 - 3 * (b : ℝ) ^ 2) := by ring
      rw [e, sqrt3_sq, show (a : ℝ) ^ 2 - (b : ℝ) ^ 2 * 3 = (a : ℝ) ^ 2 - 3 * (b : ℝ) ^ 2 by ring]
      exact div_self hn

theorem sqrt3_mem_Q3 : Real.sqrt 3 ∈ Q3 := ⟨0, 1, by simp⟩

theorem rat_mem_Q3 (q : ℚ) : (q : ℝ) ∈ Q3 := ⟨q, 0, by simp⟩

/-- `√K ∉ ℚ(√3)` when neither `K` nor `3K` is a square. -/
theorem sqrt_not_mem_Q3 (K : ℕ) (h1 : ¬ IsSquare K) (h3 : ¬ IsSquare (3 * K)) : Real.sqrt K ∉ Q3 := by
  rintro ⟨a, b, hab⟩
  have hK : Real.sqrt K * Real.sqrt K = K := Real.mul_self_sqrt (by positivity)
  have hsq : ((a ^ 2 + 3 * b ^ 2 - K : ℚ) : ℝ) + ((2 * a * b : ℚ) : ℝ) * Real.sqrt 3 = 0 := by
    push_cast
    have : ((a : ℝ) + b * Real.sqrt 3) * ((a : ℝ) + b * Real.sqrt 3) = K := by rw [← hab]; exact hK
    linear_combination this - ((b : ℝ) ^ 2) * sqrt3_sq
  obtain ⟨-, h2⟩ := q3_zero hsq
  rcases mul_eq_zero.mp h2 with h | hb
  · rcases mul_eq_zero.mp h with h | ha
    · norm_num at h
    · -- a = 0: √K = b√3, so √(3K) = 3b
      apply (irrational_sqrt_natCast_iff (n := 3 * K)).mpr h3
      refine ⟨3 * b, ?_⟩
      have h3K : Real.sqrt ((3 * K : ℕ) : ℝ) = Real.sqrt 3 * Real.sqrt K := by
        push_cast
        exact Real.sqrt_mul (by norm_num) _
      rw [h3K, hab, ha]
      push_cast
      linear_combination (-(b : ℝ)) * sqrt3_sq
  · -- b = 0: √K = a
    apply (irrational_sqrt_natCast_iff (n := K)).mpr h1
    exact ⟨a, by rw [hab, hb]; simp⟩

/-- **The field `ℚ(√3, √K)` and the automorphism `√K ↦ −√K` fixing `√3`.** -/
theorem exists_field_conj (K : ℕ) (h1 : ¬ IsSquare K) (h3 : ¬ IsSquare (3 * K)) :
    ∃ (F : Subfield ℝ) (ψ : F →+* ℝ) (h3F : Real.sqrt 3 ∈ F) (hKF : Real.sqrt K ∈ F),
      ψ ⟨Real.sqrt 3, h3F⟩ = Real.sqrt 3 ∧ ψ ⟨Real.sqrt K, hKF⟩ = -Real.sqrt K := by
  have hx2 : Real.sqrt K ^ 2 ∈ Q3 := by
    rw [Real.sq_sqrt (by positivity)]
    exact_mod_cast rat_mem_Q3 (K : ℚ)
  obtain ⟨F, ψ, hEF, hxF, hψx, hψE⟩ := exists_conj Q3 (Real.sqrt K) hx2 (sqrt_not_mem_Q3 K h1 h3)
  exact ⟨F, ψ, hEF sqrt3_mem_Q3, hxF, hψE _ sqrt3_mem_Q3, hψx⟩

/-- **The field `ℚ(√3)` and its automorphism `√3 ↦ −√3`** (for the radicand `K = 3`). -/
theorem exists_field_conj3 :
    ∃ (F : Subfield ℝ) (ψ : F →+* ℝ) (h3F : Real.sqrt 3 ∈ F), ψ ⟨Real.sqrt 3, h3F⟩ = -Real.sqrt 3 := by
  have hx2 : Real.sqrt 3 ^ 2 ∈ (algebraMap ℚ ℝ).fieldRange := by
    rw [Real.sq_sqrt (by norm_num)]
    exact ⟨3, by norm_num⟩
  have hx : Real.sqrt 3 ∉ (algebraMap ℚ ℝ).fieldRange := by
    rintro ⟨q, hq⟩
    exact irr3 ⟨q, hq⟩
  obtain ⟨F, ψ, -, hxF, hψx, -⟩ := exists_conj _ (Real.sqrt 3) hx2 hx
  exact ⟨F, ψ, hxF, hψx⟩

end Erdos634.Draft.QuadConj

#print axioms Erdos634.Draft.QuadConj.exists_field_conj
#print axioms Erdos634.Draft.QuadConj.exists_field_conj3
