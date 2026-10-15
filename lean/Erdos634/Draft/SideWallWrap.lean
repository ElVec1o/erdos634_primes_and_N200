import Erdos634.SideWall

namespace Erdos634.Draft.SideWallWrap
open Erdos634.SideWall Erdos634.Geometry Erdos634.Placement
open Erdos634.ChainInstance Erdos634.OrientBridge

theorem wrap_side_walk {N : ℕ} (D : Dissection N) (dir : Plane →ₗ[ℝ] ℝ)
    (n : ℕ) (hn : 1 ≤ n) (E : ℕ → Fin N × Fin 3) (a b c : ℝ)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hmeet : ∀ j, j + 1 < n → edgeEast D dir (E j) = edgeWest D dir (E (j + 1)))
    (hlen : ∀ j ∈ Finset.range n,
      edgeEnd D dir (E j) - edgePos D dir (E j) ∈ ({a, b, c} : Finset ℝ)) :
    edgeEnd D dir (E (n - 1)) - edgePos D dir (E 0)
      = ((Finset.range n).filter
          (fun j => edgeEnd D dir (E j) - edgePos D dir (E j) = a)).card * a
        + ((Finset.range n).filter
          (fun j => edgeEnd D dir (E j) - edgePos D dir (E j) = b)).card * b
        + ((Finset.range n).filter
          (fun j => edgeEnd D dir (E j) - edgePos D dir (E j) = c)).card * c :=
  side_walk D dir n hn E a b c hab hac hbc hmeet hlen

example : True := trivial
#print axioms wrap_side_walk

end Erdos634.Draft.SideWallWrap
