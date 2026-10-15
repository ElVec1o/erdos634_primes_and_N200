import Erdos634.EquilateralConic

namespace Erdos634.Draft.EquilateralConicWrap
open Erdos634.EquilateralConic

theorem wrap_conicform_2pi3 (s t N q : ℤ) (hst : t * s = 3 * N)
    (hq : (t - s) ^ 2 + 16 * N = q ^ 2) :
    ∃ u v : ℤ, u * v = 16 * N ^ 2 ∧ (2 : ℤ) ∣ (u + v) ∧ (u + v) / 2 - 5 * N = s ^ 2
      ∧ s ∣ 3 * N :=
  conicform_2pi3 s t N q hst hq

example : True := trivial
#print axioms wrap_conicform_2pi3

end Erdos634.Draft.EquilateralConicWrap
