import Erdos634.SecondEdge
import Erdos634.PinLemma

/-!
# Arithmetic cores of the statement that the tile below the a-edge of T₁ has a vertex at P

Arithmetic cores cited:

* `SecondEdge.other_angles_of_alpha`: a tile presenting α at one vertex presents
  β at one other and γ at the third (pure Walls13 combinatorics, `decide`).
* `SecondEdge.angleOfFlanks_flanks`: `angleOfFlanks` inverts `flanks` (`decide`).
* `SecondEdge.at_most_one_straight`: at most one straight angle beside a γ
  (angle arithmetic: 2γ+π > 2π).
* `PinLemma.no_through_tile`: a through-tile at a flanked junction is impossible
  (the straight-angle contribution alone makes the sum exceed π, by `linarith`).

The geometric part (T₂'s chord trace ending at P, tile identification at J) is not part of this file.

Standard axioms, no `sorry`.
-/

namespace Erdos634.Draft.NoTPWrap

open Erdos634.SecondEdge Erdos634.Walls13 Erdos634.PinLemma

/-- A tile presenting α at one vertex presents β and γ at the other two. -/
theorem no_tp_alpha_forces_beta_gamma :
    angleOfFlanks (flanks Angle.alpha).1 (opposite Angle.alpha) = some Angle.gamma ∧
    angleOfFlanks (flanks Angle.alpha).2 (opposite Angle.alpha) = some Angle.beta :=
  other_angles_of_alpha

/-- `angleOfFlanks` inverts `flanks`: the angle is determined by its two non-opposite edges. -/
theorem no_tp_angle_of_flanks_inverts (A : Angle) :
    angleOfFlanks (flanks A).1 (flanks A).2 = some A :=
  angleOfFlanks_flanks A

/-- At most one straight angle sits beside a γ: 2γ+π and γ+2π both exceed 2π. -/
theorem no_tp_at_most_one_straight {al be ga : ℝ}
    (hal : 0 < al) (hbe : 0 < be)
    (hsum : 3 * al + 2 * be = Real.pi) (hga : ga = 2 * al + be) :
    2 * Real.pi < ga + ga + Real.pi ∧ 2 * Real.pi < ga + Real.pi + Real.pi :=
  at_most_one_straight hal hbe hsum hga

/-- A through-tile at a flanked junction is impossible: its π contribution makes
    the sum exceed π with the two positive flanks. -/
theorem no_tp_no_through_tile (flankW flankE rest : ℝ)
    (hW : 0 < flankW) (hE : 0 < flankE) (hrest : 0 ≤ rest)
    (hsum : flankW + flankE + (Real.pi + rest) = Real.pi) : False :=
  no_through_tile flankW flankE rest hW hE hrest hsum

-- Non-vacuity: α = π/4, β = π/8 satisfy 3α+2β = π; γ = 2α+β = 5π/8.
-- `other_angles_of_alpha` is a finite `decide` over Walls13 types; non-vacuity is trivial.
-- `at_most_one_straight` witness: al = π/4, be = π/8.

#print axioms no_tp_alpha_forces_beta_gamma
#print axioms no_tp_at_most_one_straight
#print axioms no_tp_no_through_tile

end Erdos634.Draft.NoTPWrap
