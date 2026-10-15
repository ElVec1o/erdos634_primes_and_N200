import Erdos634.FanKill

/-!
# FanKill — fan killing and semigroup gap: wrapper

Key results:
- `wedge_is_beta`: wedge at a|c junction is exactly β
- `no_exact_fan`: no multiple kα equals β
- `fan_remainder`: remainder β - ⌊β/α⌋α is in (0, α)
- `fan_kill`: nothing fits in the remainder
- `fan_dies`: assembled (4,2) junction kill
- `overrun_is_one`: c - b = 1 for all f
- `one_is_gap`: run of length 1 cannot be covered
- `two_gap_contract`: only gaps b−a and c−b arise

No sorry, standard axioms.
-/

namespace Erdos634.Draft.FanKillWrap

open Erdos634.FanKill Real

theorem fk_wedge_is_beta (a b g p : ℝ) (hg : g = 2*a + b) (hp : p = 3*a + 2*b) :
    p - g - a = b :=
  wedge_is_beta a b g p hg hp

theorem fk_no_exact_fan (a b : ℝ) (hsum : 3*a + 2*b = π)
    (hirr : ¬ ∃ r : ℚ, a = (r : ℝ) * π) (k : ℕ) : (k : ℝ) * a ≠ b :=
  no_exact_fan a b hsum hirr k

theorem fk_fan_remainder (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hsum : 3*a + 2*b = π) (hirr : ¬ ∃ r : ℚ, a = (r : ℝ) * π) :
    0 < b - (⌊b / a⌋₊ : ℝ) * a ∧ b - (⌊b / a⌋₊ : ℝ) * a < a :=
  fan_remainder a b ha hb hsum hirr

theorem fk_fan_kill (a r θ : ℝ) (hr : r < a) (hθ : a ≤ θ) : ¬ θ ≤ r :=
  fan_kill a r θ hr hθ

theorem fk_fan_dies (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hsum : 3*a + 2*b = π) (hirr : ¬ ∃ r : ℚ, a = (r : ℝ) * π)
    (θ : ℝ) (hθ : a ≤ θ) :
    ¬ θ ≤ b - (⌊b / a⌋₊ : ℝ) * a :=
  fan_dies a b ha hb hsum hirr θ hθ

theorem fk_overrun_is_one (f : ℤ) : f ^ 2 - (f ^ 2 - 1) = 1 :=
  overrun_is_one f

theorem fk_one_is_gap (f x y z : ℕ) (hf : 2 ≤ f)
    (h : x * f + y * (f ^ 2 - 1) + z * f ^ 2 = 1) : False :=
  one_is_gap f x y z hf h

theorem fk_two_gap_contract (f x y z : ℕ) (hf : 3 ≤ f) :
    (x * f + y * (f * f - 1) + z * (f * f) = f * f - 1 - f → False) ∧
    (x * f + y * (f ^ 2 - 1) + z * f ^ 2 = 1 → False) :=
  two_gap_contract f x y z hf

-- Non-vacuity: overrun is arithmetic
example : (5 : ℤ) ^ 2 - (5 ^ 2 - 1) = 1 := fk_overrun_is_one 5

#print axioms fk_fan_dies
#print axioms fk_one_is_gap
#print axioms fk_two_gap_contract

end Erdos634.Draft.FanKillWrap
