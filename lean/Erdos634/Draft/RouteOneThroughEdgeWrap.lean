import Erdos634.RouteOneThroughEdge

namespace Erdos634.Draft.RouteOneThroughEdgeWrap
open Erdos634.Geometry
open Erdos634.RouteOne

theorem wrap_route_one_flank_from_configuration {N : ℕ} (D : Dissection N)
    (i j : Fin N) (V A : Plane)
    (hij : i ≠ j)
    (hne0 : (D.tile i).localAngle V ≠ 0)
    (hne2pi : (D.tile i).localAngle V ≠ 2 * Real.pi)
    (habovei : ∀ q : Plane, q ∈ (D.tile i).carrier → 0 ≤ (q - V) 1)
    (habovej : ∀ q : Plane, q ∈ (D.tile j).carrier → 0 ≤ (q - V) 1)
    (hserve : ∀ δ : ℝ, 0 < δ → ∃ q : Plane, q ∈ (D.tile i).carrier ∧
      0 < (q - V) 0 ∧ (q - V) 1 ≤ δ * ((q - V) 0))
    (mj : Fin 3)
    (hjseg : openSegment ℝ V A
      ⊆ openSegment ℝ ((D.tile j).pts (mj + 1)) ((D.tile j).pts (mj + 2)))
    (hAy : (A - V) 1 = 0) (hAx : (A - V) 0 < 0)
    (hVint : V ∈ interior D.target.carrier) (hAcar : A ∈ D.target.carrier) :
    ∃ m : Fin 3, (D.tile i).pts m = V ∧
      ((((D.tile i).pts (m + 1) - V) 1 = 0 ∧ 0 < ((D.tile i).pts (m + 1) - V) 0) ∨
       (((D.tile i).pts (m + 2) - V) 1 = 0 ∧ 0 < ((D.tile i).pts (m + 2) - V) 0)) :=
  route_one_flank_from_configuration D i j V A hij hne0 hne2pi habovei habovej hserve mj hjseg
    hAy hAx hVint hAcar

example : True := trivial
#check @wrap_route_one_flank_from_configuration

end Erdos634.Draft.RouteOneThroughEdgeWrap
