import Erdos634.RouteOne

namespace Erdos634.Draft.RouteOneWrap
open Erdos634.RouteOne
open Erdos634.Geometry

theorem wrap_EscapeData_ofWall {N : ℕ} (D : Dissection N) (V : Plane) (b : Fin N)
    (hV : V ∈ interior D.target.carrier)
    (hVb : V ∈ (D.tile b).carrier)
    (hb : (D.tile b).localAngle V = Real.pi)
    (hcard : ({j | (D.tile j).localAngle V = Real.pi} : Finset (Fin N)).card = 1)
    (hbelow : ∀ q : Plane, q ∈ (D.tile b).carrier → (q - V) 1 ≤ 0)
    (pick : ℕ → Plane) (g : ℕ → Fin N)
    (hg : ∀ n, pick n ∈ (D.tile (g n)).carrier)
    (hx : ∀ n, 0 < (pick n - V) 0)
    (hslope : ∀ n, (pick n - V) 1 ≤ (1 / (n + 1 : ℝ)) * ((pick n - V) 0))
    (hnear : ∀ n, dist (pick n) V < 1 / (n + 1 : ℝ))
    (hpos : ∀ n, 0 < (pick n - V) 1)
    (habove : ∀ n : ℕ, ∀ q : Plane, q ∈ (D.tile (g n)).carrier →
      0 ≤ (q - V) 1 ∨ g n = b) :
    Nonempty (EscapeData D) :=
  EscapeData.ofWall D V b hV hVb hb hcard hbelow pick g hg hx hslope hnear hpos habove

example : True := trivial
#check @wrap_EscapeData_ofWall

end Erdos634.Draft.RouteOneWrap
