import Erdos634.WbtwTraceInTarget

namespace Erdos634.Draft.WbtwTraceInTargetWrap
open Erdos634.ChordTraceReal Erdos634.Geometry

theorem wrap_wbtw_of_mem_tile_trace {N : ℕ} (D : Erdos634.Geometry.Dissection N)
    (f : Plane →ₗ[ℝ] ℝ) (c : ℝ) {P Q : Plane}
    (hPQ : D.target.carrier ∩ {x | f x = c} = segment ℝ P Q)
    (k : Fin N) {x : Plane} (hx : x ∈ (D.tile k).carrier ∩ {y | f y = c}) :
    Wbtw ℝ P x Q :=
  wbtw_of_mem_tile_trace D f c hPQ k hx

example : True := trivial
#check @wrap_wbtw_of_mem_tile_trace

end Erdos634.Draft.WbtwTraceInTargetWrap
