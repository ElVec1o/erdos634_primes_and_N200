import Erdos634.TPTwoTiles

namespace Erdos634.Draft.TPTwoTilesWrap
open Erdos634.FCTwoTiles Erdos634.TPTwoTiles

theorem wrap_N_ne_two {α : ℝ} {N : ℕ}
    (hα : 0 < α) (hβ : 0 < Real.pi / 3 - α)
    (hN : N = 2 → TwoPieceCut α (Real.pi / 3 - α) (2 * Real.pi / 3)) : N ≠ 2 :=
  N_ne_two hα hβ hN

example : True := trivial
#check @wrap_N_ne_two

end Erdos634.Draft.TPTwoTilesWrap
