import Erdos634.OrientWord

namespace Erdos634.Draft.OrientWordWrap
open Erdos634.Geometry Erdos634.Inflation Erdos634.Inflation.Orient
open Erdos634.OrientWord

theorem wrap_corner_anchored_word {N : ℕ} (D : Dissection N) (n : ℕ) (o : ℕ → Orient)
    (tile : ℕ → Fin N) (p : ℕ → Plane) (α β γ : ℝ) (hα : 0 < α) (hγ : γ = 2 * α + β)
    (hπ : 3 * α + 2 * β = Real.pi)
    (hfront : ∀ j, j + 1 < n → p j ∈ frontier D.target.carrier)
    (hvert : ∀ j, j + 1 < n → p j ∉ Set.range D.target.pts)
    (hne : ∀ j, j + 1 < n → tile j ≠ tile (j + 1))
    (hBG : ∀ j, j + 1 < n → o j = Orient.BG → (D.tile (tile j)).localAngle (p j) = γ)
    (hGB : ∀ j, j + 1 < n → o (j + 1) = Orient.GB →
      (D.tile (tile (j + 1))).localAngle (p j) = γ)
    (hseed : (word n o).head? = some Orient.BG) :
    word n o = List.replicate (word n o).length Orient.BG :=
  corner_anchored_word D n o tile p α β γ hα hγ hπ hfront hvert hne hBG hGB hseed

example : True := trivial
#print axioms wrap_corner_anchored_word

end Erdos634.Draft.OrientWordWrap
