import Erdos634.SolvCore

namespace Erdos634.Draft.SolvCoreWrap
open Erdos634.SolvCore

theorem wrap_solv_iff (d e a b c : ℤ) (hd : 1 ≤ d) (he : 1 ≤ e) (hb : b = d * e ^ 2)
    (ha : 0 < a) (hcop : IsCoprime a e) (htriple : c ^ 2 = a ^ 2 + a * b + b ^ 2) (hc : 0 < c) :
    e ∣ (a + b - c) ↔
      ∃ j : ℤ, d < j ∧ j < 2 * d ∧ 2 ∣ e * j ∧
        4 * a * (j - d) = e ^ 2 * (2 * d - j) * (2 * d + j) ∧ 2 * c = 2 * a + e ^ 2 * j :=
  solv_iff d e a b c hd he hb ha hcop htriple hc

example : True := trivial
#check @wrap_solv_iff

end Erdos634.Draft.SolvCoreWrap
