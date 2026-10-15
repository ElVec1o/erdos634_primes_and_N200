-- No sorry, no native_decide.
-- `lemmaS` (LemmaSAll) instantiated at tiles with R₀ ≠ 0:
--   n = 14, a = (2,5,7), p = 7 : EVEN branch (m = 2), half entry 2·a₂ = n, R₀ = span{e₂}
--   n = 35, a = (3,3,29), p = 7: ODD branch, equal entries a₀ = a₁, R₀ = span{e₀ - e₁}
-- The conclusion is extracted non-trivially (R ≠ ⊥, specific vectors in/out, and an independent direct
-- computation of R ⊆ span{e₂} at n = 14 that does not use lemmaS).
-- LemmaSStatement is pure algebra on ℚ³: it has NO dissection in its hypotheses (hypotheses: a_i ≥ 1, Σ a = n,
-- gcd = 1, p prime ≥ 7, p ∣ n), so no CongruentDissection is needed or forced.
import Mathlib
import Erdos634.Draft.LemmaSAll

namespace Erdos634.Draft.GCLLemmaS

open Erdos634.LemmaS Erdos634.LemmaSAll

/-! ## n = 14, a = (2,5,7) -/

/-- hypotheses of `LemmaSStatement` all discharged by computation; conclusion is `lemmaS`'s. -/
theorem R14 : relSpace 14 ![2, 5, 7] = trivSpace 14 ![2, 5, 7] :=
  lemmaS 14 ![2, 5, 7] (by intro i; fin_cases i <;> decide) (by simp [Fin.sum_univ_three])
    (by decide) 7 (by norm_num) le_rfl (by norm_num)

theorem e2_mem_triv : (Pi.single 2 1 : Fin 3 → ℚ) ∈ trivSpace 14 ![2, 5, 7] := by
  apply Submodule.subset_span
  right
  exact ⟨2, by decide, rfl⟩

/-- R₀ ≠ ⊥ here (non-trivial tile). -/
theorem triv14_ne_bot : trivSpace 14 ![2, 5, 7] ≠ ⊥ := by
  intro h
  have := e2_mem_triv
  rw [h, Submodule.mem_bot] at this
  have := congrFun this 2
  simp at this

/-- R₀ ⊆ span{e₂} (the generators: no equal entries, only i = 2 has 2 a_i = n). -/
theorem triv14_le : trivSpace 14 ![2, 5, 7] ≤ Submodule.span ℚ {(Pi.single 2 1 : Fin 3 → ℚ)} := by
  unfold trivSpace
  apply Submodule.span_le.mpr
  rintro v (⟨i, j, hij, h, -⟩ | ⟨i, h, rfl⟩)
  · exfalso; fin_cases i <;> fin_cases j <;> simp_all
  · fin_cases i
    · simp at h
    · simp at h
    · exact Submodule.subset_span rfl

/-- **Extracted consequence of `lemmaS` at (14; 2,5,7)**: every relation vector has e₀ = e₁ = 0, and e₂ is free. -/
theorem R14_consequence :
    (∀ e ∈ relSpace 14 ![2, 5, 7], e 0 = 0 ∧ e 1 = 0) ∧
    (Pi.single 2 1 : Fin 3 → ℚ) ∈ relSpace 14 ![2, 5, 7] ∧
    relSpace 14 ![2, 5, 7] ≠ ⊥ ∧
    (Pi.single 0 1 : Fin 3 → ℚ) ∉ relSpace 14 ![2, 5, 7] ∧
    (Pi.single 1 1 : Fin 3 → ℚ) ∉ relSpace 14 ![2, 5, 7] := by
  have hle : ∀ e ∈ relSpace 14 ![2, 5, 7], e 0 = 0 ∧ e 1 = 0 := by
    intro e he
    rw [R14] at he
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp (triv14_le he)
    simp
  refine ⟨hle, R14 ▸ e2_mem_triv, R14 ▸ triv14_ne_bot, fun h => ?_, fun h => ?_⟩
  · have := (hle _ h).1; simp at this
  · have := (hle _ h).2; simp at this

/-- **Independent check** (does not use `lemmaS`): the two equations k = 1, k = 3 alone already force
e₀ = e₁ = 0 for e ∈ R(2,5,7; 14).  So the extracted `e 0 = 0 ∧ e 1 = 0` agrees with a direct computation. -/
theorem R14_direct (e : Fin 3 → ℚ) (he : e ∈ relSpace 14 ![2, 5, 7]) : e 0 = 0 ∧ e 1 = 0 := by
  rw [mem_relSpace_Z (by norm_num)] at he
  have h1 := he 1 (by norm_num)
  have h3 := he 3 (by norm_num)
  simp [sawZ] at h1 h3
  norm_num at h1 h3
  constructor <;> linarith

/-- the two computations agree: the direct bound and the lemma give the same R, on the nose
(R ⊆ span{e₂} directly, and ⊇ from lemmaS). -/
theorem R14_eq_span : relSpace 14 ![2, 5, 7] = Submodule.span ℚ {(Pi.single 2 1 : Fin 3 → ℚ)} := by
  apply le_antisymm
  · intro e he
    obtain ⟨h0, h1⟩ := R14_direct e he
    refine Submodule.mem_span_singleton.mpr ⟨e 2, ?_⟩
    ext i; fin_cases i <;> simp [h0, h1]
  · rw [R14]; exact Submodule.span_le.mpr (by
      intro v hv; rw [Set.mem_singleton_iff] at hv; subst hv; exact e2_mem_triv)

/-! ## n = 35, a = (3,3,29): odd branch, equal entries -/

theorem R35 : relSpace 35 ![3, 3, 29] = trivSpace 35 ![3, 3, 29] :=
  lemmaS 35 ![3, 3, 29] (by intro i; fin_cases i <;> decide) (by simp [Fin.sum_univ_three])
    (by decide) 7 (by norm_num) le_rfl (by norm_num)

theorem diff_mem_triv :
    (Pi.single 0 1 - Pi.single 1 1 : Fin 3 → ℚ) ∈ trivSpace 35 ![3, 3, 29] := by
  apply Submodule.subset_span
  left
  exact ⟨0, 1, by decide, rfl, rfl⟩

theorem triv35_le : trivSpace 35 ![3, 3, 29] ≤
    Submodule.span ℚ {(Pi.single 0 1 - Pi.single 1 1 : Fin 3 → ℚ)} := by
  unfold trivSpace
  apply Submodule.span_le.mpr
  rintro v (⟨i, j, hij, h, rfl⟩ | ⟨i, h, rfl⟩)
  · have hneg : (Pi.single 1 1 - Pi.single 0 1 : Fin 3 → ℚ) =
        (-1 : ℚ) • (Pi.single 0 1 - Pi.single 1 1 : Fin 3 → ℚ) := by
      ext k; fin_cases k <;> simp
    fin_cases i <;> fin_cases j <;> first
      | exact absurd rfl hij
      | exact Submodule.subset_span rfl
      | (show (Pi.single 1 1 - Pi.single 0 1 : Fin 3 → ℚ) ∈ _
         rw [hneg]; exact Submodule.smul_mem _ _ (Submodule.subset_span rfl))
      | (exfalso; revert h; decide)
  · exfalso; revert h; fin_cases i <;> decide

/-- consequence of `lemmaS` at (35; 3,3,29). -/
theorem R35_consequence :
    (∀ e ∈ relSpace 35 ![3, 3, 29], e 2 = 0 ∧ e 0 + e 1 = 0) ∧
    (Pi.single 0 1 - Pi.single 1 1 : Fin 3 → ℚ) ∈ relSpace 35 ![3, 3, 29] ∧
    relSpace 35 ![3, 3, 29] ≠ ⊥ ∧
    (Pi.single 0 1 : Fin 3 → ℚ) ∉ relSpace 35 ![3, 3, 29] := by
  have hle : ∀ e ∈ relSpace 35 ![3, 3, 29], e 2 = 0 ∧ e 0 + e 1 = 0 := by
    intro e he
    rw [R35] at he
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp (triv35_le he)
    simp
  refine ⟨hle, R35 ▸ diff_mem_triv, fun h => ?_, fun h => ?_⟩
  · have := R35 ▸ diff_mem_triv
    rw [h, Submodule.mem_bot] at this
    have := congrFun this 0; simp at this
  · have := (hle _ h).2; simp at this

end Erdos634.Draft.GCLLemmaS

#print axioms Erdos634.Draft.GCLLemmaS.R14_consequence
#print axioms Erdos634.Draft.GCLLemmaS.R14_direct
#print axioms Erdos634.Draft.GCLLemmaS.R14_eq_span
#print axioms Erdos634.Draft.GCLLemmaS.R35_consequence
