import Erdos634.B84Geom

namespace Erdos634.Draft.B84GeomWrap

open Erdos634.B84
open Erdos634.Geometry
open Erdos634.Draft.FDBBaseBetaE1 (HasSides)

noncomputable section

/-- Delegation: `b84_exists` — an explicit `CongruentDissection 84` of tile (2,3,4) with
    target sides 24, 24, 42. -/
theorem wrap_b84_exists : ∃ D : CongruentDissection 84, HasSides D.model 2 3 4 ∧
    dist (D.target.pts 1) (D.target.pts 2) = 24 ∧
    dist (D.target.pts 2) (D.target.pts 0) = 24 ∧
    dist (D.target.pts 0) (D.target.pts 1) = 42 :=
  b84_exists

example : True := trivial

#print axioms wrap_b84_exists

end

end Erdos634.Draft.B84GeomWrap
