/-
Witnesses for Prop K-a (each hypothesis set is satisfied non-vacuously).
* `H3K_witness` / `theoremKa_witness`: the weight system e = (1, -1, 0) on (1, 1, 298) (n = 300, r = 2, j = 1, a coincidence a_P = a_Q)
  satisfies the hypothesis `H3K` with e != 0, so `theoremKa_lab` is applied non-vacuously.
* `lemmaS5_Ka_*` : n = 300 (tiles (7,157,136) shape A, (7,143,150) shape B, (3,13,284) odd entry divisible by 3, (1,1,298) coincidence),
  n = 900 (r = 2, j = 2), n = 1500 (r = 3, j = 1).
* `trivSpace_ne_bot_Ka_300` : R_0 != 0 on the coincidence tile, so the equations are not `bot = bot`.
Data (exact integers, from an exact search): the same statement fails at n = 60 (r = 1, j = 1: 8 tiles).
No sorry / native_decide.
-/
import Mathlib
import Erdos634.Draft.GA2SH

open scoped BigOperators
open Finset
open scoped Classical

namespace Erdos634.GA2SI

open Erdos634.LemmaSC (bracket)
open Erdos634.LemmaSPhi (chi)
open Erdos634.LemmaS (relSpace trivSpace)
open Erdos634.GA2SC Erdos634.GA2SG Erdos634.GA2SH

theorem H3K_witness : H3K 2 1 1 1 298 (1 : ℂ) (-1) 0 := by
  intro ψ hψ η2 η3 hodd
  simp

theorem theoremKa_witness :
    ∀ x : ℕ, ¬ 5 ∣ x →
      (if 1 = x then (1 : ℂ) else 0) + (if 1 = x then (-1 : ℂ) else 0) + (if 298 = x then (0 : ℂ) else 0) = 0 :=
  theoremKa_lab 2 1 le_rfl le_rfl 1 1 298 1 (-1) 0 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by norm_num) (by decide) H3K_witness

theorem lemmaS5_Ka_300_shapeA :
    relSpace (5 ^ 2 * (2 ^ 2 * 3 ^ 1)) ![7, 157, 136] = trivSpace (5 ^ 2 * (2 ^ 2 * 3 ^ 1)) ![7, 157, 136] :=
  lemmaS5_Ka 2 1 le_rfl le_rfl _ (by intro i; fin_cases i <;> decide) (by simp [Fin.sum_univ_three]) (by decide)

theorem lemmaS5_Ka_300_shapeB :
    relSpace (5 ^ 2 * (2 ^ 2 * 3 ^ 1)) ![7, 143, 150] = trivSpace (5 ^ 2 * (2 ^ 2 * 3 ^ 1)) ![7, 143, 150] :=
  lemmaS5_Ka 2 1 le_rfl le_rfl _ (by intro i; fin_cases i <;> decide) (by simp [Fin.sum_univ_three]) (by decide)

theorem lemmaS5_Ka_300_leftover :
    relSpace (5 ^ 2 * (2 ^ 2 * 3 ^ 1)) ![3, 13, 284] = trivSpace (5 ^ 2 * (2 ^ 2 * 3 ^ 1)) ![3, 13, 284] :=
  lemmaS5_Ka 2 1 le_rfl le_rfl _ (by intro i; fin_cases i <;> decide) (by simp [Fin.sum_univ_three]) (by decide)

theorem lemmaS5_Ka_300_double :
    relSpace (5 ^ 2 * (2 ^ 2 * 3 ^ 1)) ![1, 1, 298] = trivSpace (5 ^ 2 * (2 ^ 2 * 3 ^ 1)) ![1, 1, 298] :=
  lemmaS5_Ka 2 1 le_rfl le_rfl _ (by intro i; fin_cases i <;> decide) (by simp [Fin.sum_univ_three]) (by decide)

theorem lemmaS5_Ka_900 :
    relSpace (5 ^ 2 * (2 ^ 2 * 3 ^ 2)) ![7, 457, 436] = trivSpace (5 ^ 2 * (2 ^ 2 * 3 ^ 2)) ![7, 457, 436] :=
  lemmaS5_Ka 2 2 le_rfl (by norm_num) _ (by intro i; fin_cases i <;> decide) (by simp [Fin.sum_univ_three]) (by decide)

theorem lemmaS5_Ka_1500 :
    relSpace (5 ^ 3 * (2 ^ 2 * 3 ^ 1)) ![7, 743, 750] = trivSpace (5 ^ 3 * (2 ^ 2 * 3 ^ 1)) ![7, 743, 750] :=
  lemmaS5_Ka 3 1 (by norm_num) le_rfl _ (by intro i; fin_cases i <;> decide) (by simp [Fin.sum_univ_three]) (by decide)

theorem trivSpace_ne_bot_Ka_300 : trivSpace (5 ^ 2 * (2 ^ 2 * 3 ^ 1)) ![1, 1, 298] ≠ ⊥ := by
  intro h
  have hv : (Pi.single 0 1 - Pi.single 1 1 : Fin 3 → ℚ) ∈ trivSpace (5 ^ 2 * (2 ^ 2 * 3 ^ 1)) ![1, 1, 298] :=
    Submodule.subset_span (Or.inl ⟨0, 1, by decide, by decide, rfl⟩)
  rw [h, Submodule.mem_bot] at hv
  have := congrFun hv 0
  simp at this

end Erdos634.GA2SI

#print axioms Erdos634.GA2SI.H3K_witness
#print axioms Erdos634.GA2SI.theoremKa_witness
#print axioms Erdos634.GA2SI.lemmaS5_Ka_300_shapeA
#print axioms Erdos634.GA2SI.lemmaS5_Ka_300_shapeB
#print axioms Erdos634.GA2SI.lemmaS5_Ka_300_leftover
#print axioms Erdos634.GA2SI.lemmaS5_Ka_300_double
#print axioms Erdos634.GA2SI.lemmaS5_Ka_900
#print axioms Erdos634.GA2SI.lemmaS5_Ka_1500
#print axioms Erdos634.GA2SI.trivSpace_ne_bot_Ka_300
