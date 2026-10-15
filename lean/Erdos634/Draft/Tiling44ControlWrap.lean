import Erdos634.Tiling44Control

namespace Erdos634.Draft.Tiling44ControlWrap
open Erdos634.Geometry Erdos634.CertCoord Erdos634.Tiling44Bridge Erdos634.SixPlacements
open Erdos634.Tiling44Control

theorem wrap_tile0_is_the_placement :
    (dissection.tile idx0).pts 0 = v0 ∧
    (dissection.tile idx0).pts 1 = v0 + (16:ℝ) • d0 ∧
    (dissection.tile idx0).pts 2 = placeThird v0 d0 16 32 24 ∧
    0 < cross d0 ((dissection.tile idx0).pts 2 - v0) :=
  tile0_is_the_placement

example : True := trivial
#print axioms wrap_tile0_is_the_placement

end Erdos634.Draft.Tiling44ControlWrap
