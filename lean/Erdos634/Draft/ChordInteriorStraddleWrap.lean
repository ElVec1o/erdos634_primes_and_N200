import Erdos634.ChordInteriorStraddle

namespace Erdos634.Draft.ChordInteriorStraddleWrap
open Erdos634.Geometry Erdos634.ChordTraceReal

theorem wrap_interior_on_line_straddles (T : Tri) (f : Plane →ₗ[ℝ] ℝ) (hf : f ≠ 0) (c : ℝ)
    {y : Plane} (hy : y ∈ interior T.carrier) (hfy : f y = c) :
    (∃ i, f (T.pts i) < c) ∧ (∃ j, c < f (T.pts j)) :=
  interior_on_line_straddles T f hf c hy hfy

example : True := trivial
#print axioms wrap_interior_on_line_straddles

end Erdos634.Draft.ChordInteriorStraddleWrap
