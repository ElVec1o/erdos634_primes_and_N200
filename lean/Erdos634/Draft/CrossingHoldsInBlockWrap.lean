import Erdos634.CrossingHoldsInBlock

namespace Erdos634.Draft.CrossingHoldsInBlockWrap
open Erdos634.CrossingHoldsInBlock

theorem wrap_crossing_holds_in_block
    (noCross alphaUp : ℕ → Prop) (l : ℕ)
    (equiv : ∀ k, noCross k ↔ alphaUp k)
    (climb : ∀ j, inBlock l j → alphaUp j) :
    ∀ k, inBlock l k → noCross k :=
  crossing_holds_in_block noCross alphaUp l equiv climb

example : True := trivial
#print axioms wrap_crossing_holds_in_block

end Erdos634.Draft.CrossingHoldsInBlockWrap
