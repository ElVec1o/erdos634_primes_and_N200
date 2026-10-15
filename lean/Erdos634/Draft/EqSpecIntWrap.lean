import Erdos634.EqSpecInt

namespace Erdos634.Draft.EqSpecIntWrap
open Erdos634.EqSpecInt

theorem wrap_eqspecint_core (N S a b s t q X Y : ℤ) (hab : a * b ≠ 0) (hS : S ≠ 0)
    (hXY : X * Y = 3 * (a * b)) (hXsubY : X - Y = 2 * (a - b))
    (hs : s * X = 3 * S) (ht : t * Y = 3 * S)
    (harea : S ^ 2 = N * (a * b)) (hq : S * q = 2 * N * (a + b)) :
    s * t = 3 * N ∧ (t - s) ^ 2 + 16 * N = q ^ 2 :=
  eqspecint_core N S a b s t q X Y hab hS hXY hXsubY hs ht harea hq

example : True := trivial
#print axioms wrap_eqspecint_core

end Erdos634.Draft.EqSpecIntWrap
