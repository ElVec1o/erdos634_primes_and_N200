import Erdos634.ChordFinsetBaseCase

namespace Erdos634.Draft.ChordFinsetBaseCaseWrap
open Erdos634.Geometry Erdos634.ChordTraceReal

theorem wrap_not_mem_gap_of_far_precedes {P p Q Rk Sk y : Plane}
    (hPp : Wbtw ℝ P p Q) (hpQ : p ≠ Q)
    (hgo : Wbtw ℝ P Rk Sk) (hSp : Wbtw ℝ P Sk p)
    (hyPQ : Wbtw ℝ P y Q) (hlocal : Wbtw ℝ Rk y Sk) :
    y ∉ openSegment ℝ p Q :=
  not_mem_gap_of_far_precedes hPp hpQ hgo hSp hyPQ hlocal

example : True := trivial
#print axioms wrap_not_mem_gap_of_far_precedes

end Erdos634.Draft.ChordFinsetBaseCaseWrap
