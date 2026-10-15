/-
Witnesses for the GA2P hypotheses (each hypothesis set is satisfied non-vacuously).

* `HC_witness` / `theoremC_witness` : the weight system e = (1, -1, 0) on the tile (1, 1, 43) (n = 45, a coincidence a_0 = a_1)
  satisfies the Theorem-C hypothesis `HC 2` with e != 0, so `theoremC_classes` is applied non-vacuously.
* `lemmaS5_i0_*`  : n = 45 (tiles (1,7,37): three visible entries; (1,1,43): coincidence), n = 135.
* `lemmaS5_i2_*`  : n = 180: (97, 7, 76) = shape A (a_p = a_q + n/2, a_s = 76 = 0 mod 4), (7, 83, 90) = shape B (a_p + a_q = n/2 = a_s),
                    (3, 13, 164) = an odd entry divisible by 3 plus an even entry prime to 5 (L1 and L2 branches), (1, 1, 178) coincidence;
                    n = 540: (1, 1, 538).
* `trivSpace_ne_bot_*` : R_0 != 0 on the coincidence tiles, so the equations `relSpace = trivSpace` are not `⊥ = ⊥`.
Data (exact integers, from an exact search): the same statement fails at j = 1 (n = 30: 12 tiles, n = 60: 8 tiles).
No sorry / native_decide.
-/
import Mathlib
import Erdos634.Draft.GA2PH

open scoped BigOperators
open Finset
open scoped Classical

namespace Erdos634.GA2PI

open Erdos634.LemmaSC (bracket)
open Erdos634.LemmaSPhi (chi)
open Erdos634.LemmaS (relSpace trivSpace)
open Erdos634.GA2PD Erdos634.GA2PH

theorem HC_witness : HC 2 ![1, 1, 43] ![(1 : ℂ), -1, 0] := by
  intro ψ hψ η2 η3 hodd
  simp [Fin.sum_univ_three]

theorem theoremC_witness :
    ∀ t, ¬ 5 ∣ (![1, 1, 43] : Fin 3 → ℕ) t →
      ∑ t' ∈ (univ.filter (fun k => ¬ 5 ∣ (![1, 1, 43] : Fin 3 → ℕ) k)).filter
        (fun k => (![1, 1, 43] : Fin 3 → ℕ) k = (![1, 1, 43] : Fin 3 → ℕ) t), (![(1 : ℂ), -1, 0] : Fin 3 → ℂ) t' = 0 :=
  theoremC_classes 2 le_rfl ![1, 1, 43] ![(1 : ℂ), -1, 0] (by intro i; fin_cases i <;> decide)
    (by decide) (by decide) HC_witness

theorem lemmaS5_i0_45_visible :
    relSpace (5 ^ 1 * (2 ^ 0 * 3 ^ 2)) ![1, 7, 37] = trivSpace (5 ^ 1 * (2 ^ 0 * 3 ^ 2)) ![1, 7, 37] :=
  lemmaS5_i0 2 le_rfl _ (by intro i; fin_cases i <;> decide) (by simp [Fin.sum_univ_three]) (by decide)

theorem lemmaS5_i0_45_double :
    relSpace (5 ^ 1 * (2 ^ 0 * 3 ^ 2)) ![1, 1, 43] = trivSpace (5 ^ 1 * (2 ^ 0 * 3 ^ 2)) ![1, 1, 43] :=
  lemmaS5_i0 2 le_rfl _ (by intro i; fin_cases i <;> decide) (by simp [Fin.sum_univ_three]) (by decide)

theorem lemmaS5_i0_135 :
    relSpace (5 ^ 1 * (2 ^ 0 * 3 ^ 3)) ![1, 1, 133] = trivSpace (5 ^ 1 * (2 ^ 0 * 3 ^ 3)) ![1, 1, 133] :=
  lemmaS5_i0 3 (by norm_num) _ (by intro i; fin_cases i <;> decide) (by simp [Fin.sum_univ_three]) (by decide)

theorem lemmaS5_i2_180_shapeA :
    relSpace (5 ^ 1 * (2 ^ 2 * 3 ^ 2)) ![97, 7, 76] = trivSpace (5 ^ 1 * (2 ^ 2 * 3 ^ 2)) ![97, 7, 76] :=
  lemmaS5_i2 2 le_rfl _ (by intro i; fin_cases i <;> decide) (by simp [Fin.sum_univ_three]) (by decide)

theorem lemmaS5_i2_180_shapeB :
    relSpace (5 ^ 1 * (2 ^ 2 * 3 ^ 2)) ![7, 83, 90] = trivSpace (5 ^ 1 * (2 ^ 2 * 3 ^ 2)) ![7, 83, 90] :=
  lemmaS5_i2 2 le_rfl _ (by intro i; fin_cases i <;> decide) (by simp [Fin.sum_univ_three]) (by decide)

theorem lemmaS5_i2_180_leftover :
    relSpace (5 ^ 1 * (2 ^ 2 * 3 ^ 2)) ![3, 13, 164] = trivSpace (5 ^ 1 * (2 ^ 2 * 3 ^ 2)) ![3, 13, 164] :=
  lemmaS5_i2 2 le_rfl _ (by intro i; fin_cases i <;> decide) (by simp [Fin.sum_univ_three]) (by decide)

theorem lemmaS5_i2_180_double :
    relSpace (5 ^ 1 * (2 ^ 2 * 3 ^ 2)) ![1, 1, 178] = trivSpace (5 ^ 1 * (2 ^ 2 * 3 ^ 2)) ![1, 1, 178] :=
  lemmaS5_i2 2 le_rfl _ (by intro i; fin_cases i <;> decide) (by simp [Fin.sum_univ_three]) (by decide)

theorem lemmaS5_i2_540 :
    relSpace (5 ^ 1 * (2 ^ 2 * 3 ^ 3)) ![1, 1, 538] = trivSpace (5 ^ 1 * (2 ^ 2 * 3 ^ 3)) ![1, 1, 538] :=
  lemmaS5_i2 3 (by norm_num) _ (by intro i; fin_cases i <;> decide) (by simp [Fin.sum_univ_three]) (by decide)

theorem trivSpace_ne_bot_i0_45 : trivSpace (5 ^ 1 * (2 ^ 0 * 3 ^ 2)) ![1, 1, 43] ≠ ⊥ := by
  intro h
  have hv : (Pi.single 0 1 - Pi.single 1 1 : Fin 3 → ℚ) ∈ trivSpace (5 ^ 1 * (2 ^ 0 * 3 ^ 2)) ![1, 1, 43] :=
    Submodule.subset_span (Or.inl ⟨0, 1, by decide, by decide, rfl⟩)
  rw [h, Submodule.mem_bot] at hv
  have := congrFun hv 0
  simp at this

theorem trivSpace_ne_bot_i2_180 : trivSpace (5 ^ 1 * (2 ^ 2 * 3 ^ 2)) ![1, 1, 178] ≠ ⊥ := by
  intro h
  have hv : (Pi.single 0 1 - Pi.single 1 1 : Fin 3 → ℚ) ∈ trivSpace (5 ^ 1 * (2 ^ 2 * 3 ^ 2)) ![1, 1, 178] :=
    Submodule.subset_span (Or.inl ⟨0, 1, by decide, by decide, rfl⟩)
  rw [h, Submodule.mem_bot] at hv
  have := congrFun hv 0
  simp at this

end Erdos634.GA2PI

#print axioms Erdos634.GA2PI.HC_witness
#print axioms Erdos634.GA2PI.theoremC_witness
#print axioms Erdos634.GA2PI.lemmaS5_i0_45_visible
#print axioms Erdos634.GA2PI.lemmaS5_i0_45_double
#print axioms Erdos634.GA2PI.lemmaS5_i0_135
#print axioms Erdos634.GA2PI.lemmaS5_i2_180_shapeA
#print axioms Erdos634.GA2PI.lemmaS5_i2_180_shapeB
#print axioms Erdos634.GA2PI.lemmaS5_i2_180_leftover
#print axioms Erdos634.GA2PI.lemmaS5_i2_180_double
#print axioms Erdos634.GA2PI.lemmaS5_i2_540
#print axioms Erdos634.GA2PI.trivSpace_ne_bot_i0_45
#print axioms Erdos634.GA2PI.trivSpace_ne_bot_i2_180
