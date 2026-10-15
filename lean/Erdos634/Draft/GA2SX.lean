/-
GA2S, witnesses for the T-rows (Prop K-b with an entry divisible by 3 at j >= 2; Prop K-c with an entry divisible by 3: T odd, or T even at j >= 2).
Nothing vacuous:
* `H0_witness`, `kb_lab_witness` : the labelled hypothesis `H0 2 2 1 5 219 e` with e = (0, 1, 0) != 0 (the middle entry is divisible by 5, so its bracket vanishes),
  tile (1, 5, 219), n = 225, T = 219 = 3 * 73; `kb_lab` is applied to it (non-vacuous: all numeric hypotheses of `kb_lab` hold).
* `H1_witness`, `kc_lab_witness_*` : the same for `H1` at n = 150 (T = 3 odd, tile (3, 7, 140)) and n = 450 (T = 432 even, tile (7, 11, 432); T = 9 odd).
* `lemmaS5_Kb3_*`, `lemmaS5_Kc3_*` : relSpace = trivSpace on concrete tiles (n = 225, 675, 1125; n = 150, 450, 750).
Note: on these tiles trivSpace = bot (no coincidence a_i = a_j is possible when an entry is divisible by 3 and 5 !| it, and 2 a_i = n would force a_i divisible by 5),
so the content of the theorems is relSpace = bot.  The same statement fails at n = 30, 60 (an exact computation).
No sorry / native_decide.
-/
import Mathlib
import Erdos634.Draft.GA2ST

open scoped BigOperators
open Finset
open scoped Classical

namespace Erdos634.GA2SX

open Erdos634.LemmaSC (bracket)
open Erdos634.LemmaSPhi (chi)
open Erdos634.LemmaS (relSpace trivSpace)
open Erdos634.GA2SL Erdos634.GA2SM Erdos634.GA2SN Erdos634.GA2SP Erdos634.GA2SS Erdos634.GA2ST

theorem H0_witness : H0 2 2 1 5 219 (0 : ℂ) 1 0 := by
  intro ψ hψ η hodd
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  rw [Erdos634.LemmaSPhi.bracket_p_dvd (p := 5) (r := 2) (by norm_num) (Erdos634.GA2PA.not5_dvd' 0 2) hψ _ 5 (by norm_num)]
  simp

theorem kb_lab_witness :
    ∀ x : ℕ, ¬ 5 ∣ x →
      (if 1 = x then (0 : ℂ) else 0) + (if 5 = x then (1 : ℂ) else 0) + (if 219 = x then (0 : ℂ) else 0) = 0 :=
  kb_lab 2 2 le_rfl le_rfl 1 5 219 0 1 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) H0_witness

theorem H1_witness : H1 2 1 3 5 142 (0 : ℂ) 1 0 := by
  intro ψ hψ η hodd
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  rw [Erdos634.LemmaSPhi.bracket_p_dvd (p := 5) (r := 2) (by norm_num) (Erdos634.GA2PA.not5_dvd' 1 1) hψ _ 5 (by norm_num)]
  simp

theorem kc_lab_witness :
    ∀ x : ℕ, ¬ 5 ∣ x →
      (if 3 = x then (0 : ℂ) else 0) + (if 5 = x then (1 : ℂ) else 0) + (if 142 = x then (0 : ℂ) else 0) = 0 :=
  kc_lab 2 1 le_rfl le_rfl 3 5 142 0 1 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (Or.inl ⟨by norm_num, by norm_num⟩) H1_witness

theorem lemmaS5_Kb3_225_a :
    relSpace (5 ^ 2 * (2 ^ 0 * 3 ^ 2)) ![1, 2, 222] = trivSpace (5 ^ 2 * (2 ^ 0 * 3 ^ 2)) ![1, 2, 222] :=
  Erdos634.GA2SN.lemmaS5_Kb3 2 2 le_rfl le_rfl _ (by intro i; fin_cases i <;> decide) (by simp [Fin.sum_univ_three])
    (by decide) ⟨2, by decide, by decide⟩

theorem lemmaS5_Kb3_225_b :
    relSpace (5 ^ 2 * (2 ^ 0 * 3 ^ 2)) ![7, 11, 207] = trivSpace (5 ^ 2 * (2 ^ 0 * 3 ^ 2)) ![7, 11, 207] :=
  Erdos634.GA2SN.lemmaS5_Kb3 2 2 le_rfl le_rfl _ (by intro i; fin_cases i <;> decide) (by simp [Fin.sum_univ_three])
    (by decide) ⟨2, by decide, by decide⟩

theorem lemmaS5_Kb3_225_five :
    relSpace (5 ^ 2 * (2 ^ 0 * 3 ^ 2)) ![5, 1, 219] = trivSpace (5 ^ 2 * (2 ^ 0 * 3 ^ 2)) ![5, 1, 219] :=
  Erdos634.GA2SN.lemmaS5_Kb3 2 2 le_rfl le_rfl _ (by intro i; fin_cases i <;> decide) (by simp [Fin.sum_univ_three])
    (by decide) ⟨2, by decide, by decide⟩

theorem lemmaS5_Kb3_675 :
    relSpace (5 ^ 2 * (2 ^ 0 * 3 ^ 3)) ![1, 2, 672] = trivSpace (5 ^ 2 * (2 ^ 0 * 3 ^ 3)) ![1, 2, 672] :=
  Erdos634.GA2SN.lemmaS5_Kb3 2 3 le_rfl (by norm_num) _ (by intro i; fin_cases i <;> decide) (by simp [Fin.sum_univ_three])
    (by decide) ⟨2, by decide, by decide⟩

theorem lemmaS5_Kb3_1125 :
    relSpace (5 ^ 3 * (2 ^ 0 * 3 ^ 2)) ![1, 2, 1122] = trivSpace (5 ^ 3 * (2 ^ 0 * 3 ^ 2)) ![1, 2, 1122] :=
  Erdos634.GA2SN.lemmaS5_Kb3 3 2 (by norm_num) le_rfl _ (by intro i; fin_cases i <;> decide) (by simp [Fin.sum_univ_three])
    (by decide) ⟨2, by decide, by decide⟩

theorem lemmaS5_Kc3_150_Todd :
    relSpace (5 ^ 2 * (2 ^ 1 * 3 ^ 1)) ![3, 7, 140] = trivSpace (5 ^ 2 * (2 ^ 1 * 3 ^ 1)) ![3, 7, 140] :=
  lemmaS5_Kc3 2 1 le_rfl le_rfl _ (by intro i; fin_cases i <;> decide) (by simp [Fin.sum_univ_three])
    (by decide) ⟨0, by decide, by decide, Or.inr (by decide)⟩

theorem lemmaS5_Kc3_450_Teven :
    relSpace (5 ^ 2 * (2 ^ 1 * 3 ^ 2)) ![7, 11, 432] = trivSpace (5 ^ 2 * (2 ^ 1 * 3 ^ 2)) ![7, 11, 432] :=
  lemmaS5_Kc3 2 2 le_rfl (by norm_num) _ (by intro i; fin_cases i <;> decide) (by simp [Fin.sum_univ_three])
    (by decide) ⟨2, by decide, by decide, Or.inl le_rfl⟩

theorem lemmaS5_Kc3_450_Todd :
    relSpace (5 ^ 2 * (2 ^ 1 * 3 ^ 2)) ![9, 13, 428] = trivSpace (5 ^ 2 * (2 ^ 1 * 3 ^ 2)) ![9, 13, 428] :=
  lemmaS5_Kc3 2 2 le_rfl (by norm_num) _ (by intro i; fin_cases i <;> decide) (by simp [Fin.sum_univ_three])
    (by decide) ⟨0, by decide, by decide, Or.inr (by decide)⟩

theorem lemmaS5_Kc3_750 :
    relSpace (5 ^ 3 * (2 ^ 1 * 3 ^ 1)) ![3, 7, 740] = trivSpace (5 ^ 3 * (2 ^ 1 * 3 ^ 1)) ![3, 7, 740] :=
  lemmaS5_Kc3 3 1 (by norm_num) le_rfl _ (by intro i; fin_cases i <;> decide) (by simp [Fin.sum_univ_three])
    (by decide) ⟨0, by decide, by decide, Or.inr (by decide)⟩

end Erdos634.GA2SX

#print axioms Erdos634.GA2SX.H0_witness
#print axioms Erdos634.GA2SX.kb_lab_witness
#print axioms Erdos634.GA2SX.H1_witness
#print axioms Erdos634.GA2SX.kc_lab_witness
#print axioms Erdos634.GA2SX.lemmaS5_Kb3_225_a
#print axioms Erdos634.GA2SX.lemmaS5_Kb3_225_b
#print axioms Erdos634.GA2SX.lemmaS5_Kb3_225_five
#print axioms Erdos634.GA2SX.lemmaS5_Kb3_675
#print axioms Erdos634.GA2SX.lemmaS5_Kb3_1125
#print axioms Erdos634.GA2SX.lemmaS5_Kc3_150_Todd
#print axioms Erdos634.GA2SX.lemmaS5_Kc3_450_Teven
#print axioms Erdos634.GA2SX.lemmaS5_Kc3_450_Todd
#print axioms Erdos634.GA2SX.lemmaS5_Kc3_750
