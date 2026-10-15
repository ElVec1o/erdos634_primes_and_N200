-- Draft/FluxDRow13Witness.lean: witness for Draft/FluxDRow13.lean.
--
-- No tiling of the base-(α+β) target is known, so `Row13.boundary` and `Row13.rational` are
-- conditional at the geometric level.  What is witnessed is the algebra they run: at the rational tile
-- `s = 1/2` (`(a, b, c) = (2, 3, 4)`), legs `X = 6`, base `Y = sX = 3`, the two boundary identities
-- hold with the integers `(K, M) = (3, 1)` (`K(c+b−a) = 15 = Y + 2X`, `M(a+b+c) = 9 = 2X − Y`), and
-- `s = (K−M)/(K+M) = 1/2`.  This is not a tiling.
import Erdos634.Draft.FluxDRow13

namespace Erdos634.Draft.FluxDRow13Witness

theorem algebra_s_half :
    (3 : ℝ) * (4 + 3 - 2) = 3 + 6 + 6 ∧ (1 : ℝ) * (2 + 3 + 4) = 6 + 6 - 3 ∧
      (2 : ℝ) / 4 = ((3 : ℝ) - 1) / ((3 : ℝ) + 1) ∧ (3 : ℝ) = (1 / 2) * 6 := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩

end Erdos634.Draft.FluxDRow13Witness

#print axioms Erdos634.Draft.FluxDRow13Witness.algebra_s_half
