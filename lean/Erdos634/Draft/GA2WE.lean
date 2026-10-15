/-
GA2W, part E: non-vacuity witnesses for KbJ1Lab (n = 75) and KcJ1Lab (n = 150), in the style of GA2UI.d3_nonvacuous.
  `kb_witness_H0` / `kb_nonvacuous` : r = 2, n = 75, tile (5, 67, 3):  every numerical hypothesis of KbJ1Lab holds
        (5 + 67 + 3 = 75 = 5^2 * 3, 3 !| 5, 3 !| 67, 3 | 3, 5 !| 3), H0 holds with the NONZERO weight (1, 0, 0) on the 5-divisible
        (invisible) entry 5, and `kbJ1_lab` is applied to it.
  `kc_witness_H1` / `kc_nonvacuous` : r = 2, n = 150, tile (5, 139, 6): 5 + 139 + 6 = 150, 5, 139 odd, 6 even, gcd = 1, 3 | 6, 5 !| 6;
        H1 holds with weight (1, 0, 0); `kcJ1_lab` is applied.
  `kb_surviving_instance` / `kc_surviving_instance` : the surviving configurations (X = Y mod 5^r with Leg X = -Leg Y, resp. P = Q mod 5^r)
        occur: n = 75 tile (1, 26, 48) and n = 150 tile (1, 101, 48); all arithmetic hypotheses of `kb_eta1` / `kc_eta1` hold there
        (weights zero, which is what the atoms force).
Formalization of paper-level mathematics; no sorry / native_decide.
-/
import Mathlib
import Erdos634.Draft.GA2WD

open scoped BigOperators
open Finset
open scoped Classical

namespace Erdos634.GA2WE

open Erdos634.GA2SL (H0)
open Erdos634.GA2SP (H1)

theorem kb_witness_H0 : H0 2 1 5 67 3 (1 : ℂ) 0 0 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  intro ψ hψ η hodd
  rw [Erdos634.LemmaSPhi.bracket_p_dvd (p := 5) (r := 2) (by norm_num) (Erdos634.GA2PA.not5_dvd' 0 1) hψ _ 5
    (by norm_num)]
  ring

theorem kb_nonvacuous :
    ∀ x : ℕ, ¬ 5 ∣ x →
      (if 5 = x then (1 : ℂ) else 0) + (if 67 = x then (0 : ℂ) else 0) + (if 3 = x then (0 : ℂ) else 0) = 0 :=
  Erdos634.GA2WC.kbJ1_lab 2 5 67 3 1 0 0 le_rfl (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) kb_witness_H0

theorem kc_witness_H1 : H1 2 1 5 139 6 (1 : ℂ) 0 0 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  intro ψ hψ η hodd
  rw [Erdos634.LemmaSPhi.bracket_p_dvd (p := 5) (r := 2) (by norm_num) (Erdos634.GA2PA.not5_dvd' 1 1) hψ _ 5
    (by norm_num)]
  ring

theorem kc_nonvacuous :
    ∀ x : ℕ, ¬ 5 ∣ x →
      (if 5 = x then (1 : ℂ) else 0) + (if 139 = x then (0 : ℂ) else 0) + (if 6 = x then (0 : ℂ) else 0) = 0 :=
  Erdos634.GA2WD.kcJ1_lab 2 5 139 6 1 0 0 le_rfl (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) kc_witness_H1

/-- the surviving K-b configuration at n = 75, tile (1, 26, 48): all arithmetic hypotheses of `kb_eta1` hold (t = 16) -/
theorem kb_surviving_instance : H0 2 1 1 26 (3 * 16) 0 0 0 → (0 : ℂ) = 0 := by
  intro H
  have := Erdos634.GA2WC.kb_eta1 2 le_rfl 1 26 16 0 0 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by decide) rfl H
  exact this

/-- the surviving K-c configuration at n = 150, tile (1, 101, 48): all arithmetic hypotheses of `kc_eta1` hold (s = 8) -/
theorem kc_surviving_instance : H1 2 1 1 101 (6 * 8) 0 0 0 → (0 : ℂ) + 0 = 0 := by
  intro H
  exact Erdos634.GA2WD.kc_eta1 2 le_rfl 1 101 8 0 0 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) H

end Erdos634.GA2WE

#print axioms Erdos634.GA2WE.kb_witness_H0
#print axioms Erdos634.GA2WE.kb_nonvacuous
#print axioms Erdos634.GA2WE.kc_witness_H1
#print axioms Erdos634.GA2WE.kc_nonvacuous
#print axioms Erdos634.GA2WE.kb_surviving_instance
#print axioms Erdos634.GA2WE.kc_surviving_instance
