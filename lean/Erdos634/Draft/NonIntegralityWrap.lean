import Erdos634.NonIntegrality

namespace Erdos634.Draft.NonIntegralityWrap
open Erdos634.NonIntegrality

theorem wrap_k_not_dvd (a k c : ℤ) (ha : 0 < a) (hk : 0 < k) (hc : 0 < c)
    (hcop : IsCoprime a k) (heq : c ^ 2 = a ^ 2 + a * k ^ 2 + (k ^ 2) ^ 2) :
    ¬ (k ∣ (a + k ^ 2 - c)) :=
  k_not_dvd a k c ha hk hc hcop heq

example : True := trivial
#print axioms wrap_k_not_dvd

end Erdos634.Draft.NonIntegralityWrap
