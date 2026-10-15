-- Draft/FluxDRow4Witness.lean: non-vacuity witnesses for `Draft/FluxDRow4.lean`.
--
-- No tiling of the base-α target of the `γ = 2α` tile is exhibited, so `Row4.P5`, `Row4.not_two_mod_four`
-- and `Row4.prime_leg_words` are conditional at the geometric level. The shape-free input
-- `Row4.flux_signs` is witnessed on a real 4-tile dissection of the (4,5,6) triangle
-- (`Draft/FluxRow4Witness.flux_signs_456`). Here:
-- * `P5_alg_456`: the hypotheses of the arithmetic core `Row4.P5_alg` with `(a, b, c) = (4, 5, 6)`
--   (`κ = cos α = 3/4`), `X = 120`, `S₁ = −12`, `S₂ = 60`, `N = 720`, and its conclusion evaluated:
--   `M = 12`, `M′ = 60`, `720 = 12·60`, `36 < 60`, `c/a = 72/48`.
-- * `L7_2`, `L7_3`: the hypothesis of `Row4.L7` is met by both of its conclusions at `k = 2` (`N = 5`,
--   tile `(4, 5, 6)`) and `k = 3` (`N = 7`, tile `(9, 7, 12)`): `k` b-edges and `a + c`.
import Erdos634.Draft.FluxDRow4

open scoped Classical

namespace Erdos634.Draft.FluxDRow4Witness

open Erdos634.Geometry

/-- **`Row4.P5_alg` on the (4,5,6), `X = 120`, `N = 720` core**: `M = 12`, `M′ = 60`. -/
theorem P5_alg_456 :
    0 < -(-12 : ℤ) ∧ 0 < (60 : ℤ) ∧
      (((-(-12 : ℤ)) : ℤ) : ℝ) * (4 + 2 * (3 / 4) * 4) = 120 ∧
      ((60 : ℤ) : ℝ) * (2 * (3 / 4) * 4 - 4) = 120 ∧
      ((720 : ℕ) : ℤ) = -(-12 : ℤ) * 60 ∧ 3 * (-(-12 : ℤ)) < 60 ∧
      2 * (3 / 4 : ℝ) = (((60 : ℤ) : ℝ) + ((-(-12 : ℤ)) : ℤ)) / (((60 : ℤ) : ℝ) - ((-(-12 : ℤ)) : ℤ)) :=
  Row4.P5_alg (a := 4) (X := 120) (κ := 3 / 4) (S₁ := -12) (S₂ := 60) (N := 720)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

/-- **L7 at `k = 2`** (`N = 5`, tile `(k², N, k(k+1)) = (4, 5, 6)`, leg `kN = 10`): both leg words
`2b` and `a + c` satisfy the hypothesis. -/
theorem L7_2 : 2 * (2 * 2 + 1) = 0 * 2 ^ 2 + 2 * (2 * 2 + 1) + 0 * (2 * (2 + 1)) ∧
    2 * (2 * 2 + 1) = 1 * 2 ^ 2 + 0 * (2 * 2 + 1) + 1 * (2 * (2 + 1)) := by norm_num

/-- **L7 at `k = 3`** (`N = 7`, tile `(9, 7, 12)`, leg `21`): `3b` and `a + c`. -/
theorem L7_3 : 3 * (2 * 3 + 1) = 0 * 3 ^ 2 + 3 * (2 * 3 + 1) + 0 * (3 * (3 + 1)) ∧
    3 * (2 * 3 + 1) = 1 * 3 ^ 2 + 0 * (2 * 3 + 1) + 1 * (3 * (3 + 1)) := by norm_num

/-- `Row4.L7` applied at `k = 3` to the word `a + c` returns the second alternative. -/
theorem L7_3_applied : ((1 : ℕ) = 0 ∧ (0 : ℕ) = 3 ∧ (1 : ℕ) = 0) ∨ ((1 : ℕ) = 1 ∧ (0 : ℕ) = 0 ∧ (1 : ℕ) = 1) :=
  Row4.L7 (k := 3) (p := 1) (q := 0) (r := 1) (by norm_num) L7_3.2

end Erdos634.Draft.FluxDRow4Witness

#print axioms Erdos634.Draft.FluxDRow4Witness.P5_alg_456
#print axioms Erdos634.Draft.FluxDRow4Witness.L7_2
#print axioms Erdos634.Draft.FluxDRow4Witness.L7_3
#print axioms Erdos634.Draft.FluxDRow4Witness.L7_3_applied
