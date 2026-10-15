import Erdos634.RouteOneStepBridge

namespace Erdos634.Draft.RouteOneStepBridgeWrap
open Erdos634.Geometry
open Erdos634.RouteOneStepBridge

theorem wrap_march_from_wall {N : ℕ} {D : Dissection N} {w : Plane}
    (S : Set Plane) (hne : S.Nonempty) (hw : w ≠ 0)
    (tl : Plane → Fin N) (cn of : Plane → Fin 3)
    (hof : ∀ V ∈ S, of V = 1 ∨ of V = 2)
    (hhead : ∀ V ∈ S, (D.tile (tl V)).pts (cn V) = V)
    (hfoot : ∀ V ∈ S, (D.tile (tl V)).pts (cn V + of V) = V + w)
    (hnext : ∀ V ∈ S, V + w ∈ S) : False :=
  march_from_wall S hne hw tl cn of hof hhead hfoot hnext

example : True := trivial
#check @wrap_march_from_wall

end Erdos634.Draft.RouteOneStepBridgeWrap
