import Erdos634.PinPlumbing

namespace Erdos634.Draft.PinPlumbingWrap
open Erdos634.Geometry
open Erdos634.PinPlumbing

theorem wrap_junction_equation {N : ℕ} (D : Dissection N) (model : Tri)
    (hcong : ∀ i, model.Congruent (D.tile i))
    {p : Plane} (hp : p ∈ frontier D.target.carrier) (hv : p ∉ Set.range D.target.pts)
    (iW iE : Fin N) (hWE : iW ≠ iE)
    (hAW : 0 < (D.tile iW).localAngle p) (hAE : 0 < (D.tile iE).localAngle p) :
    ∃ x y z : ℕ,
      (x : ℝ) * cornerAngle (model.pts 1) (model.pts 0) (model.pts 2)
        + y * cornerAngle (model.pts 2) (model.pts 1) (model.pts 0)
        + z * cornerAngle (model.pts 0) (model.pts 2) (model.pts 1)
      = Real.pi - (D.tile iW).localAngle p - (D.tile iE).localAngle p :=
  junction_equation D model hcong hp hv iW iE hWE hAW hAE

example : True := trivial
#print axioms wrap_junction_equation

end Erdos634.Draft.PinPlumbingWrap
