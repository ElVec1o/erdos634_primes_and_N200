-- Draft/FluxDRow4L8Witness.lean: witnesses for `Draft/FluxDRow4L8.lean` and `Draft/FluxDRow4Bk.lean`
-- (corner figures, the `{a, c}` case, `R4(ii)`).
--
-- The geometric theorems (`Row4.corner_A/B`, `L8_ac`, `prime_reduced`, `bk_leg`, `not_prime`) are stated
-- for an `N`-tiling of the base-α target by the tile with `γ = 2α`; no such tiling is exhibited, so they
-- are conditional. Witnessed here:
-- * `Row4.fig_arith` at the corner figures, with the real irrational angle `α456` of the (4,5,6)
--   triangle (`cos α = 3/4`, `Draft/FluxRow4Witness`): `(1,0,0)` at a base corner, `(1,1,0)` at the apex,
--   `(1,1,1)` and `(3,1,0)` inside a side.
-- * `Row4.endpoint_of_subsegment` on a genuine segment.
-- * `Row4.lattice` on `{0, 1, 2}` (k = 3).
import Erdos634.Draft.FluxDRow4Bk
import Erdos634.Draft.FluxRow4Witness

open scoped Classical

namespace Erdos634.Draft.FluxDRow4L8Witness

open Erdos634.Geometry Erdos634.Draft.FluxRow4Witness

/-- L1 at a base corner: the figure `(1,0,0)` (one `α`). -/
theorem fig_A : ((0 : ℕ) : ℤ) + (0 : ℕ) + 2 * (0 : ℕ) = 0 ∧ ((1 : ℕ) : ℤ) - 3 * (0 : ℕ) + 2 * (0 : ℕ) = 1 :=
  Row4.fig_arith α456_irr (P := 1) (Q := 0) (R := 0) (S := 0) (T := 0) (j := 0) (k := 1)
    (by push_cast; ring)

/-- L1 at the apex: the figure `(1,1,0)` (one `α`, one `β = π − 3α`). -/
theorem fig_B : ((1 : ℕ) : ℤ) + (0 : ℕ) + 2 * (0 : ℕ) = 1 ∧ ((1 : ℕ) : ℤ) - 3 * (1 : ℕ) + 2 * (0 : ℕ) = -2 :=
  Row4.fig_arith α456_irr (P := 1) (Q := 1) (R := 0) (S := 0) (T := 0) (j := 1) (k := -2)
    (by push_cast; ring)

/-- L1 inside a side: the figures `(1,1,1)` and `(3,1,0)`. -/
theorem fig_side :
    (((1 : ℕ) : ℤ) + (0 : ℕ) + 2 * (0 : ℕ) = 1 ∧ ((1 : ℕ) : ℤ) - 3 * (1 : ℕ) + 2 * (1 : ℕ) = 0) ∧
    (((1 : ℕ) : ℤ) + (0 : ℕ) + 2 * (0 : ℕ) = 1 ∧ ((3 : ℕ) : ℤ) - 3 * (1 : ℕ) + 2 * (0 : ℕ) = 0) :=
  ⟨Row4.fig_arith α456_irr (P := 1) (Q := 1) (R := 1) (S := 0) (T := 0) (j := 1) (k := 0)
      (by push_cast; ring),
    Row4.fig_arith α456_irr (P := 3) (Q := 1) (R := 0) (S := 0) (T := 0) (j := 1) (k := 0)
      (by push_cast; ring)⟩

/-- `endpoint_of_subsegment` on the segment from `0` to `e₀`. -/
theorem endpoint_witness :
    (0 : Plane) = 0 ∨ (0 : Plane) = EuclideanSpace.single 0 (1 : ℝ) := by
  have hne : (0 : Plane) ≠ EuclideanSpace.single 0 (1 : ℝ) := by
    intro h
    have := congrArg (fun v : Plane => v 0) h
    simp at this
  exact Row4.endpoint_of_subsegment hne subset_rfl (left_mem_segment ℝ _ _)

/-- The lattice lemma on `{0, 1, 2}`. -/
theorem lattice_witness : ({0, 1, 2} : Finset ℝ) = (Finset.range 3).image (fun n : ℕ => (n : ℝ)) := by
  apply Row4.lattice 3
  · rw [Finset.card_insert_of_notMem (by norm_num), Finset.card_insert_of_notMem (by norm_num)]; rfl
  · intro x hx; simp at hx; rcases hx with rfl | rfl | rfl <;> norm_num
  · intro x hx; simp at hx; rcases hx with rfl | rfl | rfl <;> norm_num
  · intro x hx y hy hxy
    simp at hx hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;> (try norm_num at hxy) <;>
      (try norm_num)

end Erdos634.Draft.FluxDRow4L8Witness

#print axioms Erdos634.Draft.FluxDRow4L8Witness.fig_A
#print axioms Erdos634.Draft.FluxDRow4L8Witness.fig_B
#print axioms Erdos634.Draft.FluxDRow4L8Witness.fig_side
#print axioms Erdos634.Draft.FluxDRow4L8Witness.endpoint_witness
#print axioms Erdos634.Draft.FluxDRow4L8Witness.lattice_witness
