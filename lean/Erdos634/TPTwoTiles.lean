import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Erdos634.FCTwoTiles

/-!
# `N = 2` is impossible for a `2π/3` tile — analogue of `FCTwoTiles` for the TwoPiThree branch

Erdős #634.

## The gap this closes

`TSPSimilar.lean` (`reduction_tiling_complete`) requires `N > 3`; so does `G1NFinal.lean`.
`prop:reduction` therefore has an acknowledged gap at `N = 2` (and `N = 3`).  This file closes
the `N = 2` half for the TwoPiThree branch by the same cevian argument as `FCTwoTiles`.

## The argument

A `2π/3` tile has angles `(α, π/3 − α, 2π/3)` with `0 < α`, `0 < π/3 − α`, i.e.
`0 < α < π/3`.  For a 2-piece dissection there would be a cut-point `D` on the interior of a
side where the two pieces contribute angles `θ` and `π − θ`, both tile angles.

1. `angles_at_interior_point_force_right` (from `FCTwoTiles`): that forces `θ = π/2`, i.e.
   **the tile must have a right angle**.

2. `twoPiThree_no_right_angle` (below): no `2π/3` tile with `0 < α < π/3` has a right angle.
   - `α < π/3 < π/2`, so `α ≠ π/2`.
   - `π/3 − α < π/3 < π/2`, so `π/3 − α ≠ π/2`.
   - `2π/3 > π/2`, so `2π/3 ≠ π/2`.

Steps 1 and 2 contradict, so `N ≠ 2` for any `2π/3`-tile dissection.

## Scope

Steps 1 and 2 are fully formalized, zero axioms beyond the standard three, no `sorry`.
**Step 0 — that a 2-piece triangle dissection is a cevian cut — is NOT formalized**; it is
supplied as `TwoPieceCut` (imported from `FCTwoTiles`), the same interface used there.
The interface is shown non-vacuous by `rightIsoscelesCut` in `FCTwoTiles`.
-/

namespace Erdos634.TPTwoTiles

open Real Erdos634.FCTwoTiles

/-! ## Step 2: a `2π/3` tile has no right angle -/

/-- The angles of a `2π/3` tile sum to `π`. -/
theorem twoPiThree_angle_sum (α : ℝ) : α + (π / 3 - α) + 2 * π / 3 = π := by ring

/-- **No `2π/3` tile has a right angle.**
    `α` and `π/3 − α` are both less than `π/3 < π/2`; `2π/3 > π/2`. -/
theorem twoPiThree_no_right_angle {α : ℝ}
    (hα : 0 < α) (hβ : 0 < π / 3 - α) :
    α ≠ π / 2 ∧ π / 3 - α ≠ π / 2 ∧ 2 * π / 3 ≠ π / 2 := by
  refine ⟨?_, ?_, ?_⟩
  · -- α < π/3 < π/2
    intro hc; linarith [pi_pos]
  · -- π/3 − α < π/3 < π/2
    intro hc; linarith [pi_pos]
  · -- 2π/3 > π/2
    intro hc; linarith [pi_pos]

/-! ## The exclusion -/

/-- **No `2π/3` tile admits a 2-piece dissection.**
    Any such dissection would supply a `TwoPieceCut`; that cut would force a right angle in the
    tile; but a `2π/3` tile has none. -/
theorem no_two_tile_dissection {α : ℝ}
    (hα : 0 < α) (hβ : 0 < π / 3 - α)
    (c : TwoPieceCut α (π / 3 - α) (2 * π / 3)) : False := by
  obtain ⟨h1, h2, h3⟩ := twoPiThree_no_right_angle hα hβ
  have hθ : c.θ = π / 2 :=
    angles_at_interior_point_force_right c.pos₁ c.pos₂ c.pos₃ c.sum c.θ_mem c.supp_mem
  rcases c.θ_mem with hm | hm | hm
  · exact h1 (hm ▸ hθ)
  · exact h2 (hm ▸ hθ)
  · exact h3 (hm ▸ hθ)

/-- The statement in the form the chain needs: in the `2π/3` branch, if a tile count `N` is
    realized by a dissection whose 2-piece case would be a `TwoPieceCut`, then `N ≠ 2`. -/
theorem N_ne_two {α : ℝ} {N : ℕ}
    (hα : 0 < α) (hβ : 0 < π / 3 - α)
    (hN : N = 2 → TwoPieceCut α (π / 3 - α) (2 * π / 3)) : N ≠ 2 := fun hEq =>
  no_two_tile_dissection hα hβ (hN hEq)

end Erdos634.TPTwoTiles

#print axioms Erdos634.TPTwoTiles.twoPiThree_no_right_angle
#print axioms Erdos634.TPTwoTiles.no_two_tile_dissection
