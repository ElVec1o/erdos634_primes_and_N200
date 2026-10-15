/-
GA2Q, K-versions: witnesses (every hypothesis set exhibited; nothing vacuous) and negative controls.
* i = 1: n = 150 = 2*5^2*3  (r = 2, j = 1): tiles (1,1,148), (1,7,142), (1,4,145) [entry divisible by 5]; n = 450 (r = 2, j = 2): (1,1,448);
         n = 1250 = 2*5^4*... skip.  `lemmaS5_K1` instances, `trivSpace_ne_bot_K1_150`.
* i = 0: n = 75 = 5^2*3: (1,1,73); n = 225 = 5^2*3^2: (1,1,223); n = 375 = 5^3*3: (1,1,373).  `lemmaS5_K0` instances, `trivSpace_ne_bot_K0_75`.
* `theoremK0_witness` : e = (1, -1, 0) on (1,1,73) (n = 75) satisfies the hypothesis of `theoremK0_lab` with e != 0.
* Negative controls (the UNCOVERED rows): `K1_h3_fails` (150 = 1 + 2 + 147, 147 = 3 * 49: entry divisible by 3 and not by 5),
  `K0_h3_fails` (75 = 1 + 2 + 72), the hypothesis `h3` fails, so these tiles are NOT covered by `lemmaS5_K1` / `lemmaS5_K0`.
Formalization of paper-level mathematics; no sorry / native_decide.
-/
import Mathlib
import Erdos634.Draft.GA2QK5

open scoped BigOperators
open Finset
open scoped Classical

namespace Erdos634.GA2QK6

open Erdos634.LemmaS (relSpace trivSpace)
open Erdos634.GA2QK4 Erdos634.GA2QK5

theorem lemmaS5_K1_150_a :
    relSpace (5 ^ 2 * (2 ^ 1 * 3 ^ 1)) ![1, 1, 148] = trivSpace (5 ^ 2 * (2 ^ 1 * 3 ^ 1)) ![1, 1, 148] :=
  lemmaS5_K1 2 1 (by norm_num) le_rfl (Or.inl le_rfl) _ (by intro i; fin_cases i <;> decide)
    (by simp [Fin.sum_univ_three]) (by decide) (by intro t; fin_cases t <;> decide)

theorem lemmaS5_K1_150_b :
    relSpace (5 ^ 2 * (2 ^ 1 * 3 ^ 1)) ![1, 7, 142] = trivSpace (5 ^ 2 * (2 ^ 1 * 3 ^ 1)) ![1, 7, 142] :=
  lemmaS5_K1 2 1 (by norm_num) le_rfl (Or.inl le_rfl) _ (by intro i; fin_cases i <;> decide)
    (by simp [Fin.sum_univ_three]) (by decide) (by intro t; fin_cases t <;> decide)

theorem lemmaS5_K1_150_c :
    relSpace (5 ^ 2 * (2 ^ 1 * 3 ^ 1)) ![1, 4, 145] = trivSpace (5 ^ 2 * (2 ^ 1 * 3 ^ 1)) ![1, 4, 145] :=
  lemmaS5_K1 2 1 (by norm_num) le_rfl (Or.inl le_rfl) _ (by intro i; fin_cases i <;> decide)
    (by simp [Fin.sum_univ_three]) (by decide) (by intro t; fin_cases t <;> decide)

theorem lemmaS5_K1_450 :
    relSpace (5 ^ 2 * (2 ^ 1 * 3 ^ 2)) ![1, 1, 448] = trivSpace (5 ^ 2 * (2 ^ 1 * 3 ^ 2)) ![1, 1, 448] :=
  lemmaS5_K1 2 2 (by norm_num) (by norm_num) (Or.inl le_rfl) _ (by intro i; fin_cases i <;> decide)
    (by simp [Fin.sum_univ_three]) (by decide) (by intro t; fin_cases t <;> decide)

theorem lemmaS5_K0_75 :
    relSpace (5 ^ 2 * (2 ^ 0 * 3 ^ 1)) ![1, 1, 73] = trivSpace (5 ^ 2 * (2 ^ 0 * 3 ^ 1)) ![1, 1, 73] :=
  lemmaS5_K0 2 1 (by norm_num) le_rfl _ (by intro i; fin_cases i <;> decide)
    (by simp [Fin.sum_univ_three]) (by decide) (by intro t; fin_cases t <;> decide)

theorem lemmaS5_K0_225 :
    relSpace (5 ^ 2 * (2 ^ 0 * 3 ^ 2)) ![1, 1, 223] = trivSpace (5 ^ 2 * (2 ^ 0 * 3 ^ 2)) ![1, 1, 223] :=
  lemmaS5_K0 2 2 (by norm_num) (by norm_num) _ (by intro i; fin_cases i <;> decide)
    (by simp [Fin.sum_univ_three]) (by decide) (by intro t; fin_cases t <;> decide)

theorem lemmaS5_K0_375 :
    relSpace (5 ^ 3 * (2 ^ 0 * 3 ^ 1)) ![1, 1, 373] = trivSpace (5 ^ 3 * (2 ^ 0 * 3 ^ 1)) ![1, 1, 373] :=
  lemmaS5_K0 3 1 (by norm_num) le_rfl _ (by intro i; fin_cases i <;> decide)
    (by simp [Fin.sum_univ_three]) (by decide) (by intro t; fin_cases t <;> decide)

theorem trivSpace_ne_bot_K1_150 : trivSpace (5 ^ 2 * (2 ^ 1 * 3 ^ 1)) ![1, 1, 148] ≠ ⊥ := by
  intro h
  have hv : (Pi.single 0 1 - Pi.single 1 1 : Fin 3 → ℚ) ∈ trivSpace (5 ^ 2 * (2 ^ 1 * 3 ^ 1)) ![1, 1, 148] :=
    Submodule.subset_span (Or.inl ⟨0, 1, by decide, by decide, rfl⟩)
  rw [h, Submodule.mem_bot] at hv
  have := congrFun hv 0
  simp at this

theorem trivSpace_ne_bot_K0_75 : trivSpace (5 ^ 2 * (2 ^ 0 * 3 ^ 1)) ![1, 1, 73] ≠ ⊥ := by
  intro h
  have hv : (Pi.single 0 1 - Pi.single 1 1 : Fin 3 → ℚ) ∈ trivSpace (5 ^ 2 * (2 ^ 0 * 3 ^ 1)) ![1, 1, 73] :=
    Submodule.subset_span (Or.inl ⟨0, 1, by decide, by decide, rfl⟩)
  rw [h, Submodule.mem_bot] at hv
  have := congrFun hv 0
  simp at this

theorem theoremK0_witness :
    ∀ x : ℕ, ¬ 5 ∣ x → (if (1 : ℕ) = x then (1 : ℂ) else 0) + (if (1 : ℕ) = x then (-1 : ℂ) else 0) +
      (if (73 : ℕ) = x then (0 : ℂ) else 0) = 0 :=
  theoremK0_lab 2 1 (by norm_num) le_rfl 1 1 73 1 (-1) 0 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by omega) (by omega) (by omega)
    (fun ψ hψ η hodd => by simp)

theorem K1_h3_fails : ¬ (∀ t, ¬ 5 ∣ (![1, 2, 147] : Fin 3 → ℕ) t → ¬ 3 ∣ (![1, 2, 147] : Fin 3 → ℕ) t) := by
  intro h
  exact h 2 (by decide) (by decide)

theorem K0_h3_fails : ¬ (∀ t, ¬ 5 ∣ (![1, 2, 72] : Fin 3 → ℕ) t → ¬ 3 ∣ (![1, 2, 72] : Fin 3 → ℕ) t) := by
  intro h
  exact h 2 (by decide) (by decide)

end Erdos634.GA2QK6

#print axioms Erdos634.GA2QK6.lemmaS5_K1_150_a
#print axioms Erdos634.GA2QK6.lemmaS5_K1_150_b
#print axioms Erdos634.GA2QK6.lemmaS5_K1_150_c
#print axioms Erdos634.GA2QK6.lemmaS5_K1_450
#print axioms Erdos634.GA2QK6.lemmaS5_K0_75
#print axioms Erdos634.GA2QK6.lemmaS5_K0_225
#print axioms Erdos634.GA2QK6.lemmaS5_K0_375
#print axioms Erdos634.GA2QK6.trivSpace_ne_bot_K1_150
#print axioms Erdos634.GA2QK6.trivSpace_ne_bot_K0_75
#print axioms Erdos634.GA2QK6.theoremK0_witness
#print axioms Erdos634.GA2QK6.K1_h3_fails
#print axioms Erdos634.GA2QK6.K0_h3_fails
