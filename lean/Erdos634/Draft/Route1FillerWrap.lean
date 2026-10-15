import Erdos634.Route1Filler

namespace Erdos634.Draft.Route1FillerWrap
open Erdos634.Route1Filler

theorem wrap_f_four_check :
    (1 : ℤ) * 4 ^ 2 > 4 ^ 3 - 3 * 4 ^ 2 - 4 + 1 ∧ (1 : ℤ) * 4 ^ 2 < 4 ^ 3 - 3 * 4 ^ 2 + 1 :=
  f_four_check

example : True := trivial
#print axioms wrap_f_four_check

end Erdos634.Draft.Route1FillerWrap
