import Erdos634.ThickJunctionCoords

namespace Erdos634.Draft.ThickJunctionCoordsWrap
open Erdos634.ThickJunctionCoords
open Erdos634.Geometry Erdos634.CertCoord Erdos634.BaseBetaTargetCoord

theorem wrap_junction_confined_63 (t : ℝ) :
    (∀ k, (aTileBG63 t).pts k 1 ≤ apexH63) ∧
    (∀ k, (aTileGB63 t).pts k 1 ≤ apexH63) ∧
    (∀ k, (flushFillerBG63 t).pts k 1 ≤ apexH63) ∧
    (∀ k, (flushFillerGB63 t).pts k 1 ≤ apexH63) :=
  junction_confined_63 t

example : True := trivial
#print axioms wrap_junction_confined_63

end Erdos634.Draft.ThickJunctionCoordsWrap
