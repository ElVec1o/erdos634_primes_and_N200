-- Draft/PropReductionN3.lean
-- Closes the N=3 gap in prop:reduction by combining:
--   * f1_prime_free_any  (F1N3.lean) — F1/F1' shape for any prime including N=3
--   * r8_prime_free_any  (G1NFinal.lean) — F2–F4' shapes for any prime ≠ 2
--   * no_three_equilateral_twoPiThree (N3EqCase.lean) — equilateral target for N=3
--   * ISUCore.thmIsoCore — isosceles target, any prime
--   * tile_similar_prime_false (TSPSimilar.lean) — tile-similar target, any prime
-- Gives `tp_prime_excluded_ge3`: prime N ≥ 3, any target → False.
-- 0 sorry, standard axioms.

import Erdos634.Draft.TSPSimilar
import Erdos634.Draft.F1N3
import Erdos634.Draft.N3EqCase
import Erdos634.Draft.ISUCore

open scoped Classical
open Erdos634.Geometry Erdos634.Draft.TheoremPConditional
open Erdos634.Draft.LemmaCFinal (lemmaC_general)
open Erdos634.Draft.ISUReduce (not_right not_twoAlpha not_sixty not_threeTwo)

namespace Erdos634.Draft.PropReductionN3

/-- For N=3 prime with a 2π/3-tile and an irrational angle, the target not similar to the tile:
    False.  All five shape branches are excluded by the N=3-specific lemmas. -/
theorem tp_three_excluded (D : CongruentDissection 3) {α a b c : ℝ}
    (hirr : IrrPi α) (hm : D.model.TwoPiThreeData α a b c)
    (hns : ¬SimilarTM D) : False := by
  have hirr' : ∃ k, IrrPi (D.model.angleAt k) := by
    obtain ⟨σ, h0, -⟩ := hm; exact ⟨σ 0, by rw [h0]; exact hirr⟩
  rcases lemmaC_general D hirr' hns with h | h | h | h | h
  · exact not_right D hirr hm h
  · exact not_twoAlpha D hirr hm h
  · exact not_sixty D hirr hm h
  · obtain ⟨α', a', b', c', hα', hm', hc⟩ := h
    rcases hc with h | h | h | h
    · exact N3EqCase.no_three_equilateral_twoPiThree D hα' hm' h
    · exact ISUCore.thmIsoCore 3 D (by norm_num) α' a' b' c' hα' hm' h
    · exact F1N3.f1_prime_free_any D (by norm_num) hα' hm' h
    · exact G1NFinal.r8_prime_free_any D (by norm_num) (by norm_num) hα' hm' h
  · exact not_threeTwo D hirr hm h

/-- **`prop:reduction` for prime N ≥ 3.**
    For prime N ≥ 3 and a 2π/3-tile with irrational angle, any target forces False.
    Combines `TSPSimilar.reduction_tiling_complete` (N>3) with `tp_three_excluded` (N=3).
    The paper statement is strictly weaker (target is isosceles or F₁–F₄); the Lean theorem
    gives False outright, covering all prime residues and all target shapes including
    tile-similar.  N=2 is not covered (requires the TwoPieceCut topological interface). -/
theorem tp_prime_excluded_ge3 {N : ℕ} (D : CongruentDissection N) (hN : N.Prime) (h3 : 3 ≤ N)
    {α a b c : ℝ} (hirr : IrrPi α) (hm : D.model.TwoPiThreeData α a b c) : False := by
  by_cases h3lt : 3 < N
  · exact TSPSimilar.reduction_tiling_complete D hN h3lt hirr hm
  · have hN3 : N = 3 := Nat.le_antisymm (Nat.not_lt.mp h3lt) h3
    subst hN3
    by_cases hs : SimilarTM D
    · exact TSPSimilar.tile_similar_prime_false D hN hirr hm hs
    · exact tp_three_excluded D hirr hm hs

#check @tp_prime_excluded_ge3
#print axioms tp_prime_excluded_ge3

end Erdos634.Draft.PropReductionN3
