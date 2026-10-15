import Erdos634.Eq105Rational

namespace Erdos634.Draft.Eq105RationalWrap
open Erdos634.Eq105Rational

theorem wrap_eq105_not_rational_branch :
    ∀ d k : ℕ, d ∣ 6 → 0 < d → 0 < k → d * k ^ 2 ≠ 105 :=
  eq105_not_rational_branch

example : True := trivial
#print axioms wrap_eq105_not_rational_branch

end Erdos634.Draft.Eq105RationalWrap
