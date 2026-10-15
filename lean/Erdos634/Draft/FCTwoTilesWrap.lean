import Erdos634.FCTwoTiles

namespace Erdos634.Draft.FCTwoTilesWrap

open Erdos634.FCTwoTiles Real

theorem fct_three_alpha_two_beta_no_right_angle {α β : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (h : 3 * α + 2 * β = π) :
    α ≠ π / 2 ∧ β ≠ π / 2 ∧ 2 * α + β ≠ π / 2 :=
  three_alpha_two_beta_no_right_angle hα hβ h

theorem fct_no_two_tile_dissection {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (h : 3 * α + 2 * β = π)
    (c : TwoPieceCut α β (2 * α + β)) : False :=
  no_two_tile_dissection hα hβ h c

theorem fct_N_ne_two {α β : ℝ} {N : ℕ} (hα : 0 < α) (hβ : 0 < β) (h : 3 * α + 2 * β = π)
    (hN : N = 2 → TwoPieceCut α β (2 * α + β)) : N ≠ 2 :=
  N_ne_two hα hβ h hN

example : True := trivial

#print axioms fct_three_alpha_two_beta_no_right_angle
#print axioms fct_N_ne_two

end Erdos634.Draft.FCTwoTilesWrap
