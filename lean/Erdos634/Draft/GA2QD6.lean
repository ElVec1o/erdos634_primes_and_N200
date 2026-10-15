/-
Prop D, witnesses (every hypothesis set is exhibited).
* `HD_witness` / `theoremD_witness` : e = (1, -1, 0) on the tile (1, 1, 88) (n = 90, a coincidence P = Q) satisfies the Prop D hypothesis
   (with e != 0), so `theoremD_lab'` is applied non-vacuously.
* `lemmaS5_i1_*` : n = 90: (1,1,88) coincidence, (1,7,82) three entries prime to 5, (1,4,85) an entry divisible by 5, (7,13,70); n = 270: (1,1,268).
* `trivSpace_ne_bot_i1_90` : R_0 != 0 at (1,1,88), so `relSpace = trivSpace` is not `bot = bot`.
* `h3_fails_example` : the tile (1, 2, 87) at n = 90 has an entry (87) divisible by 3 and not by 5: the hypothesis of Prop D fails (this case is
   not covered by Prop D; for n = 90 it is closed by the finite certificate `GA2OFin2.gapA2_n90`).
No sorry / native_decide.
-/
import Mathlib
import Erdos634.Draft.GA2QD5

open scoped BigOperators
open Finset
open scoped Classical

namespace Erdos634.GA2QD6

open Erdos634.LemmaSC (bracket)
open Erdos634.LemmaSPhi (chi)
open Erdos634.LemmaS (relSpace trivSpace)
open Erdos634.GA2QD5

theorem theoremD_witness :
    ∀ x : ℕ, ¬ 5 ∣ x → (if (1 : ℕ) = x then (1 : ℂ) else 0) + (if (1 : ℕ) = x then (-1 : ℂ) else 0) +
      (if (88 : ℕ) = x then (0 : ℂ) else 0) = 0 :=
  theoremD_lab' 2 le_rfl 1 1 88 1 (-1) 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by omega) (by omega) (by omega) (by omega)
    (fun ψ hψ η hodd => by simp)

theorem lemmaS5_i1_90_double :
    relSpace (5 ^ 1 * (2 ^ 1 * 3 ^ 2)) ![1, 1, 88] = trivSpace (5 ^ 1 * (2 ^ 1 * 3 ^ 2)) ![1, 1, 88] :=
  lemmaS5_i1 2 le_rfl _ (by intro i; fin_cases i <;> decide) (by simp [Fin.sum_univ_three]) (by decide)
    (by intro t; fin_cases t <;> decide)

theorem lemmaS5_i1_90_three :
    relSpace (5 ^ 1 * (2 ^ 1 * 3 ^ 2)) ![1, 7, 82] = trivSpace (5 ^ 1 * (2 ^ 1 * 3 ^ 2)) ![1, 7, 82] :=
  lemmaS5_i1 2 le_rfl _ (by intro i; fin_cases i <;> decide) (by simp [Fin.sum_univ_three]) (by decide)
    (by intro t; fin_cases t <;> decide)

theorem lemmaS5_i1_90_five :
    relSpace (5 ^ 1 * (2 ^ 1 * 3 ^ 2)) ![1, 4, 85] = trivSpace (5 ^ 1 * (2 ^ 1 * 3 ^ 2)) ![1, 4, 85] :=
  lemmaS5_i1 2 le_rfl _ (by intro i; fin_cases i <;> decide) (by simp [Fin.sum_univ_three]) (by decide)
    (by intro t; fin_cases t <;> decide)

theorem lemmaS5_i1_90_five2 :
    relSpace (5 ^ 1 * (2 ^ 1 * 3 ^ 2)) ![7, 13, 70] = trivSpace (5 ^ 1 * (2 ^ 1 * 3 ^ 2)) ![7, 13, 70] :=
  lemmaS5_i1 2 le_rfl _ (by intro i; fin_cases i <;> decide) (by simp [Fin.sum_univ_three]) (by decide)
    (by intro t; fin_cases t <;> decide)

theorem lemmaS5_i1_270 :
    relSpace (5 ^ 1 * (2 ^ 1 * 3 ^ 3)) ![1, 1, 268] = trivSpace (5 ^ 1 * (2 ^ 1 * 3 ^ 3)) ![1, 1, 268] :=
  lemmaS5_i1 3 (by norm_num) _ (by intro i; fin_cases i <;> decide) (by simp [Fin.sum_univ_three]) (by decide)
    (by intro t; fin_cases t <;> decide)

theorem trivSpace_ne_bot_i1_90 : trivSpace (5 ^ 1 * (2 ^ 1 * 3 ^ 2)) ![1, 1, 88] ≠ ⊥ := by
  intro h
  have hv : (Pi.single 0 1 - Pi.single 1 1 : Fin 3 → ℚ) ∈ trivSpace (5 ^ 1 * (2 ^ 1 * 3 ^ 2)) ![1, 1, 88] :=
    Submodule.subset_span (Or.inl ⟨0, 1, by decide, by decide, rfl⟩)
  rw [h, Submodule.mem_bot] at hv
  have := congrFun hv 0
  simp at this

/-- a tile of n = 90 with an entry divisible by 3 and not by 5; Prop D's hypothesis `h3` fails. -/
theorem h3_fails_example : ¬ (∀ t, ¬ 5 ∣ (![1, 2, 87] : Fin 3 → ℕ) t → ¬ 3 ∣ (![1, 2, 87] : Fin 3 → ℕ) t) := by
  intro h
  have := h 2 (by decide)
  exact this (by decide)

end Erdos634.GA2QD6

#print axioms Erdos634.GA2QD6.theoremD_witness
#print axioms Erdos634.GA2QD6.lemmaS5_i1_90_double
#print axioms Erdos634.GA2QD6.lemmaS5_i1_90_three
#print axioms Erdos634.GA2QD6.lemmaS5_i1_90_five
#print axioms Erdos634.GA2QD6.lemmaS5_i1_90_five2
#print axioms Erdos634.GA2QD6.lemmaS5_i1_270
#print axioms Erdos634.GA2QD6.trivSpace_ne_bot_i1_90
#print axioms Erdos634.GA2QD6.h3_fails_example
