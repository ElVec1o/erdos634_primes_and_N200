import Erdos634.WbtwOrientedTrace

namespace Erdos634.Draft.WbtwOrientedTraceWrap
open Erdos634.ChordTraceReal Erdos634.Geometry

theorem wrap_oriented_trace_of_wbtw {p q r s : Plane} (hr : Wbtw ℝ p r q) (hs : Wbtw ℝ p s q) :
    ∃ r' s', segment ℝ r s = segment ℝ r' s' ∧ Wbtw ℝ p r' s' :=
  oriented_trace_of_wbtw hr hs

example : True := trivial
#check @wrap_oriented_trace_of_wbtw

end Erdos634.Draft.WbtwOrientedTraceWrap
