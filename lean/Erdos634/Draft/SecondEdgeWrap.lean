import Erdos634.SecondEdge

namespace Erdos634.Draft.SecondEdgeWrap
open Erdos634.SecondEdge

theorem wrap_selfsim_uniform (δ : ℝ) (j k : ℕ) :
    ((j + 1 : ℝ) * δ - j * δ) = ((k + 1 : ℝ) * δ - k * δ) :=
  selfsim_uniform δ j k

example : True := trivial
#print axioms wrap_selfsim_uniform

end Erdos634.Draft.SecondEdgeWrap
