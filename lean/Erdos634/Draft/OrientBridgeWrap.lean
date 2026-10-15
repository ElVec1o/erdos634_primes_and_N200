import Erdos634.OrientBridge

namespace Erdos634.Draft.OrientBridgeWrap
open Erdos634.Geometry
open Erdos634.OrientBridge

theorem wrap_no_two_gamma_at_boundary_junction {N : ℕ} (D : Dissection N) {p : Plane}
    (hp : p ∈ frontier D.target.carrier) (hv : p ∉ Set.range D.target.pts)
    (α β γ : ℝ) (hα : 0 < α) (hγ : γ = 2 * α + β) (hπ : 3 * α + 2 * β = Real.pi)
    (i j : Fin N) (hij : i ≠ j)
    (hi : (D.tile i).localAngle p = γ) (hj : (D.tile j).localAngle p = γ) : False :=
  no_two_gamma_at_boundary_junction D hp hv α β γ hα hγ hπ i j hij hi hj

example : True := trivial
#print axioms wrap_no_two_gamma_at_boundary_junction

end Erdos634.Draft.OrientBridgeWrap
