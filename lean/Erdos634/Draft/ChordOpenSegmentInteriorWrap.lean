import Erdos634.ChordOpenSegmentInterior

namespace Erdos634.Draft.ChordOpenSegmentInteriorWrap
open Erdos634.Geometry Erdos634.ChordTraceReal

theorem wrap_straddle_openSegment_interior (T : Tri) (f : Plane →ₗ[ℝ] ℝ) (c : ℝ)
    (hlo : ∃ i, f (T.pts i) < c) (hhi : ∃ j, c < f (T.pts j))
    {x y : Plane} (hx : x ∈ T.carrier) (hfx : f x = c) (hy : y ∈ T.carrier) (hfy : f y = c)
    (hxy : x ≠ y) {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    AffineMap.lineMap x y s ∈ interior T.carrier :=
  Tri.straddle_openSegment_interior T f c hlo hhi hx hfx hy hfy hxy hs0 hs1

example : True := trivial
#print axioms wrap_straddle_openSegment_interior

end Erdos634.Draft.ChordOpenSegmentInteriorWrap
