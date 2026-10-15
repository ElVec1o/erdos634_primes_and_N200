import Erdos634.RouteOneVertexKill

namespace Erdos634.Draft.RouteOneVertexKillWrap
open Erdos634.Geometry
open Erdos634.RouteOneVertexKill

theorem wrap_straight_above_forces_horizontal (P Q V : Plane) (lam : ℝ)
    (h0 : 0 < lam) (h1 : lam < 1) (hV : V = lam • P + (1 - lam) • Q)
    (hP : 0 ≤ (P - V) 1) (hQ : 0 ≤ (Q - V) 1) (hPV : (P - V) 0 ≠ 0) :
    (P - V) 1 = 0 ∧ (Q - V) 1 = 0 ∧
      ((P - V) 0 < 0 ∧ 0 < (Q - V) 0 ∨ 0 < (P - V) 0 ∧ (Q - V) 0 < 0) :=
  straight_above_forces_horizontal P Q V lam h0 h1 hV hP hQ hPV

example : True := trivial
#check @wrap_straight_above_forces_horizontal

end Erdos634.Draft.RouteOneVertexKillWrap
