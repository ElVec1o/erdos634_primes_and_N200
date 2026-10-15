import Erdos634.RogueArea

namespace Erdos634.Draft.RogueAreaWrap
open Erdos634.RogueArea

theorem wrap_deep_gives_two_bands (e f M : ℤ) (hdeep : f + 2 * e ≤ e * M) :
    f + 2 * e ≤ M * e :=
  deep_gives_two_bands e f M hdeep

example : True := trivial
#print axioms wrap_deep_gives_two_bands

end Erdos634.Draft.RogueAreaWrap
