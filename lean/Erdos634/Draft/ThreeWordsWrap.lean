import Erdos634.ThreeWords

namespace Erdos634.Draft.ThreeWordsWrap
open Erdos634.ThreeWords

theorem wrap_the_three (e f : ℤ) :
    (0 * (e * f) + e * (f ^ 2 - e ^ 2) + (2 * e) * f ^ 2 = e * (3 * f ^ 2 - e ^ 2))
      ∧ (f * (e * f) + e * (f ^ 2 - e ^ 2) + e * f ^ 2 = e * (3 * f ^ 2 - e ^ 2))
      ∧ ((2 * f) * (e * f) + e * (f ^ 2 - e ^ 2) + 0 * f ^ 2 = e * (3 * f ^ 2 - e ^ 2)) :=
  the_three e f

example : True := trivial
#print axioms wrap_the_three

end Erdos634.Draft.ThreeWordsWrap
