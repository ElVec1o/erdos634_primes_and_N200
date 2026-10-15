import Erdos634.SixtyStructure

namespace Erdos634.Draft.SixtyStructureWrap
open Erdos634.SixtyStructure

theorem wrap_top_level_pinch (D M : ℤ → ℤ) (L : ℤ)
    (htop : ∀ j, L < j → D j = 0 ∧ M j = 0) :
    D (L + 1) = 0 ∧ M (L + 1) = 0 :=
  top_level_pinch D M L htop

example : True := trivial
#print axioms wrap_top_level_pinch

end Erdos634.Draft.SixtyStructureWrap
