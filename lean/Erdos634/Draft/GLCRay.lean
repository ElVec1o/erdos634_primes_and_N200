import Mathlib.Tactic
import Erdos634.Draft.T30LC2Forward
import Erdos634.Draft.T30LPi3F6Geom

/-!
# A ray in a half-plane is determined by its angle to the boundary and its length

Set-up for G2, `T4 = T + c u`.

`ray_determined`: in the plane, let `u ≠ 0`, `h` a functional with `h u = 0`, and `w, e` with `h w < 0`, `h e ≤ 0`, the same length and the same inner
product with `u` (i.e. the same angle to `u` once lengths agree).  Then `e = w`.  (The reflection of `w` across the line `h = 0` has `h > 0`; this is
the half-plane step that fixes the second edge of the tile at a boundary vertex.)  Counterexample `ray_needs_sign`: dropping `h w < 0, h e ≤ 0` the mirror
image `e = (w0, -w1)` of `w = (w0, w1)` across `u = (1,0)` has equal length and inner product but `e ≠ w`.
-/

namespace Erdos634.GLC

open Erdos634.Geometry

theorem ray_determined (u w e : Plane) (hu : u ≠ 0) (h : Plane →ₗ[ℝ] ℝ) (hhu : h u = 0)
    (hw : h w < 0) (he : h e ≤ 0) (hn : ‖e‖ = ‖w‖) (hi : inner ℝ u e = inner ℝ u w) : e = w := by
  have hnorm : ∀ x : Plane, ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 := fun x => by
    rw [← real_inner_self_eq_norm_sq, Erdos634.C2Forward.inner_coord]; ring
  rw [Erdos634.C2Forward.inner_coord, Erdos634.C2Forward.inner_coord] at hi
  have hn2 : e 0 ^ 2 + e 1 ^ 2 = w 0 ^ 2 + w 1 ^ 2 := by rw [← hnorm, ← hnorm, hn]
  have hhw := Erdos634.Pi3F6.lin_coord h w
  have hhe := Erdos634.Pi3F6.lin_coord h e
  have hhu' := Erdos634.Pi3F6.lin_coord h u
  rw [hhu] at hhu'
  set h0 := h (EuclideanSpace.single 0 1)
  set h1 := h (EuclideanSpace.single 1 1)
  have hN0 : u 0 ^ 2 + u 1 ^ 2 ≠ 0 := by
    intro hz
    apply hu
    have a0 : u 0 = 0 := by nlinarith [sq_nonneg (u 0), sq_nonneg (u 1)]
    have a1 : u 1 = 0 := by nlinarith [sq_nonneg (u 0), sq_nonneg (u 1)]
    ext i; fin_cases i
    · simpa using a0
    · simpa using a1
  have hN : 0 < u 0 ^ 2 + u 1 ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm hN0)
  set Λ := h1 * u 0 - h0 * u 1 with hΛ
  have kw : h w * (u 0 ^ 2 + u 1 ^ 2) = Λ * (u 0 * w 1 - u 1 * w 0) := by
    rw [hhw]; linear_combination (-(u 0 * w 0 + u 1 * w 1)) * hhu'
  have ke : h e * (u 0 ^ 2 + u 1 ^ 2) = Λ * (u 0 * e 1 - u 1 * e 0) := by
    rw [hhe]; linear_combination (-(u 0 * e 0 + u 1 * e 1)) * hhu'
  have h1' : Λ * (u 0 * w 1 - u 1 * w 0) < 0 := by rw [← kw]; nlinarith
  have h2' : Λ * (u 0 * e 1 - u 1 * e 0) ≤ 0 := by rw [← ke]; nlinarith
  have hsq : (u 0 * e 1 - u 1 * e 0) ^ 2 = (u 0 * w 1 - u 1 * w 0) ^ 2 := by
    linear_combination (u 0 ^ 2 + u 1 ^ 2) * hn2 - (u 0 * e 0 + u 1 * e 1 + (u 0 * w 0 + u 1 * w 1)) * hi
  have hC : u 0 * e 1 - u 1 * e 0 = u 0 * w 1 - u 1 * w 0 := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h' | h'
    · exact h'
    · exfalso; rw [h'] at h2'; nlinarith
  have a0 : (u 0 ^ 2 + u 1 ^ 2) * (e 0 - w 0) = 0 := by
    linear_combination u 0 * hi - u 1 * hC
  have a1 : (u 0 ^ 2 + u 1 ^ 2) * (e 1 - w 1) = 0 := by
    linear_combination u 1 * hi + u 0 * hC
  have b0 := (mul_eq_zero.mp a0).resolve_left hN0
  have b1 := (mul_eq_zero.mp a1).resolve_left hN0
  ext i; fin_cases i
  · simp; linarith
  · simp; linarith

/-- Without the half-plane hypotheses the mirror image has equal length and equal inner product with `u = (1,0)`
but is different: `w = (1,1)`, `e = (1,-1)`. -/
theorem ray_needs_sign :
    (1 : ℝ) * 1 + 0 * (-1) = 1 * 1 + 0 * 1 ∧ (1 : ℝ) ^ 2 + (-1) ^ 2 = 1 ^ 2 + 1 ^ 2 ∧ ((1 : ℝ), (-1 : ℝ)) ≠ (1, 1) := by
  refine ⟨by norm_num, by norm_num, fun h => ?_⟩
  have := congrArg Prod.snd h
  norm_num at this

end Erdos634.GLC

#print axioms Erdos634.GLC.ray_determined
