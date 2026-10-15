-- Draft/FluxCSimilarWitness.lean — NON-VACUITY WITNESS for `Paper.cor_similar`
-- (Draft/FluxCSimilar.lean): `FluxPaperWitness.D357`, the scale-2 ladder of the `(3,5,7)` tile
-- (`α ∉ ℚπ`, `data357`), a real `CongruentDissection 4` whose target is the homothetic image
-- `2·T357` (`D357_sim`).  Conclusion evaluated: `N = 4 = 2²`, `μ = 2`, `¬ Nat.Prime 4`.
-- `homothety_angle_opp` is reused from `FluxRow2Witness`.  Imported directly by All.lean.
import Erdos634.Draft.FluxCSimilar
import Erdos634.Draft.FluxPaperWitness
import Erdos634.Draft.FluxRow2Witness

open scoped Classical

namespace Erdos634.Draft.FluxCSimilarWitness

open Erdos634.Geometry Erdos634.CertCoord Erdos634.Subdivision Erdos634.Draft.FluxPaperWitness
open Erdos634.Draft.FluxRow2Witness

theorem D357_target : D357.target
    = bigTri (mkPt 5 0) (mkPt (-3/2) (3 * Real.sqrt 3 / 2)) (mkPt 0 0) T357.indep 2 (by norm_num) :=
  rfl

theorem D357_hom (i : Fin 3) :
    D357.target.pts i = mkPt 5 0 + (2 : ℝ) • (T357.pts i - mkPt 5 0) := by
  rw [D357_target]
  have hi : i = 0 ∨ i = 1 ∨ i = 2 := by fin_cases i <;> simp
  rcases hi with rfl | rfl | rfl
  · rw [bigTri_pts0]
    show mkPt 5 0 = mkPt 5 0 + (2 : ℝ) • (mkPt 5 0 - mkPt 5 0)
    simp
  · rw [bigTri_pts1]
    show P (mkPt 5 0) (mkPt (-3/2) (3 * Real.sqrt 3 / 2)) (mkPt 0 0) 2 0
      = mkPt 5 0 + (2 : ℝ) • (mkPt (-3/2) (3 * Real.sqrt 3 / 2) - mkPt 5 0)
    unfold P
    push_cast
    simp
  · rw [bigTri_pts2]
    show P (mkPt 5 0) (mkPt (-3/2) (3 * Real.sqrt 3 / 2)) (mkPt 0 0) 0 2
      = mkPt 5 0 + (2 : ℝ) • (mkPt 0 0 - mkPt 5 0)
    unfold P
    push_cast
    simp

theorem D357_sim (k : Fin 3) :
    D357.target.angleAt k = D357.model.angleAt k ∧ D357.target.oppLen k = 2 * D357.model.oppLen k :=
  homothety_angle_opp T357 D357.target (mkPt 5 0) 2 (by norm_num) D357_hom k

/-- **`cor:similar` on a real dissection: `N = 4 = m²`, `m = μ = 2`, `4` not prime.** -/
theorem cor_similar_357 : ∃ m : ℕ, m = 2 ∧ 2 * 2 = m ^ 2 ∧ ¬ Nat.Prime (2 * 2) := by
  obtain ⟨m, hm, hμ, hp⟩ := Paper.cor_similar D357 α357_irr data357 D357_sim
  exact ⟨m, by exact_mod_cast hμ.symm, hm, hp⟩

/-- **`cor:similar` as printed on a real dissection: `N = 4 = M_α²`, `M_α = ±2`.** -/
theorem cor_similar_Malpha_357 : ∃ Mα : ℤ, ((2 * 2 : ℕ) : ℤ) = Mα ^ 2 ∧ (Mα = 2 ∨ Mα = -2) := by
  obtain ⟨Mα, -, hN, -⟩ := Paper.cor_similar_Malpha D357 α357_irr data357 D357_sim
  refine ⟨Mα, hN, ?_⟩
  have h4 : Mα ^ 2 = 4 := by rw [← hN]; norm_num
  have : (Mα - 2) * (Mα + 2) = 0 := by linear_combination h4
  rcases mul_eq_zero.mp this with h | h
  · left; linarith
  · right; linarith

end Erdos634.Draft.FluxCSimilarWitness

#print axioms Erdos634.Draft.FluxCSimilarWitness.cor_similar_357
#print axioms Erdos634.Draft.FluxCSimilarWitness.cor_similar_Malpha_357
