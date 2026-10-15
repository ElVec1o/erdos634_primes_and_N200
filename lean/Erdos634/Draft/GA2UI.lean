/-
Final assembly:  `gapA2_of_two_atoms : KbJ1Lab -> KcJ1Lab -> GapA2`   (`D3Lab` is `GA2UH.d3_lab`).
  `d3_witness_H1`, `d3_nonvacuous` : the hypotheses of D3Lab are satisfiable with a nonzero weight (n = 90, tile (35, 1, 54), e = (1, 0, 0)
                                     on the 5-divisible, hence invisible, entry 35), and `d3_lab` is applied to it.
No sorry / native_decide.
-/
import Mathlib
import Erdos634.Draft.GA2UH

open scoped BigOperators
open Finset
open scoped Classical

namespace Erdos634.GA2UI

open Erdos634.GA2SP (H1)

theorem gapA2_of_two_atoms (hKb : Erdos634.GA2SY.KbJ1Lab) (hKc : Erdos634.GA2SY.KcJ1Lab) :
    Erdos634.CaseA.R0c15.GapA2 :=
  Erdos634.GA2SY.gapA2_of_atoms ⟨Erdos634.GA2UH.d3_lab, hKb, hKc⟩

theorem d3_witness_H1 : H1 1 2 35 1 54 (1 : ℂ) 0 0 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  haveI : NeZero (3 ^ 2) := ⟨by norm_num⟩
  intro ψ hψ η hodd
  rw [Erdos634.LemmaSPhi.bracket_p_dvd (p := 5) (r := 1) le_rfl (Erdos634.GA2PA.not5_dvd' 1 2) hψ _ 35
    (by norm_num)]
  ring

theorem d3_nonvacuous :
    ∀ x : ℕ, ¬ 5 ∣ x →
      (if 35 = x then (1 : ℂ) else 0) + (if 1 = x then (0 : ℂ) else 0) + (if 54 = x then (0 : ℂ) else 0) = 0 := by
  have := Erdos634.GA2UH.d3_lab 2 35 1 54 1 0 0 le_rfl (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (Or.inr (Or.inr ⟨by norm_num, by norm_num⟩)) d3_witness_H1
  exact this

end Erdos634.GA2UI

#print axioms Erdos634.GA2UI.gapA2_of_two_atoms
#print axioms Erdos634.GA2UI.d3_witness_H1
#print axioms Erdos634.GA2UI.d3_nonvacuous
