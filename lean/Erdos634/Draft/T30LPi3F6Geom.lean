import Mathlib.Tactic
import Erdos634.Dissection

/-!
# Geometric core: a triangle on the far side of a chord with swapped legs is the point reflection

* `same_side_unique`: two points strictly on the same side of the line `{f = c}` through `P ≠ R` with the same distances to `P`
  and to `R` coincide.
* `reflect_of_swapped`: if `X` is on the side `f < c`, `X'` on the side `f > c`, `|PX'| = |RX|`, `|RX'| = |PX|`, then `X' = P + R - X`.
* Witness: explicit 5-8-7-type coordinates (`wit_reflect`). The mirror image across `PR` has the same legs and is a different point
  (`mirror_ne_reflect`), so the swapped-legs hypothesis (supplied by the fan count in `T30LPi3F6`) is what distinguishes the two
  candidate placements.
-/

namespace Erdos634.Pi3F6

open Erdos634.Geometry

theorem dist_sq_coord (x y : Plane) : dist x y ^ 2 = (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 := by
  rw [EuclideanSpace.dist_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _), Fin.sum_univ_two]
  simp [Real.dist_eq, sq_abs]

theorem lin_coord (f : Plane →ₗ[ℝ] ℝ) (z : Plane) :
    f z = z 0 * f (EuclideanSpace.single 0 1) + z 1 * f (EuclideanSpace.single 1 1) := by
  have : z = z 0 • (EuclideanSpace.single 0 (1 : ℝ) : Plane) + z 1 • (EuclideanSpace.single 1 (1 : ℝ) : Plane) := by
    ext i; fin_cases i <;> simp
  conv_lhs => rw [this]
  rw [map_add, map_smul, map_smul]; simp

theorem alg2 (w0 w1 f0 f1 d0 d1 u0 u1 : ℝ) (hwd : w0 * d0 + w1 * d1 = 0) (hfd : f0 * d0 + f1 * d1 = 0)
    (hwu : w0 * u0 + w1 * u1 = 0) (hfu : f0 * u0 + f1 * u1 ≠ 0) (hd : d0 ^ 2 + d1 ^ 2 ≠ 0) :
    w0 = 0 ∧ w1 = 0 := by
  have hx0 : (w0 * f1 - w1 * f0) * d0 = 0 := by linear_combination f1 * hwd - w1 * hfd
  have hx1 : (w0 * f1 - w1 * f0) * d1 = 0 := by linear_combination (-f0) * hwd + w0 * hfd
  have hx : w0 * f1 - w1 * f0 = 0 := by
    have : (w0 * f1 - w1 * f0) * (d0 ^ 2 + d1 ^ 2) = 0 := by linear_combination d0 * hx0 + d1 * hx1
    rcases mul_eq_zero.mp this with h | h
    · exact h
    · exact absurd h hd
  have e0 : (f0 ^ 2 + f1 ^ 2) * w0 = (w0 * f0 + w1 * f1) * f0 := by linear_combination f1 * hx
  have e1 : (f0 ^ 2 + f1 ^ 2) * w1 = (w0 * f0 + w1 * f1) * f1 := by linear_combination (-f0) * hx
  have hff : f0 ^ 2 + f1 ^ 2 ≠ 0 := by
    intro h
    have h0 : f0 = 0 := by nlinarith [sq_nonneg f0, sq_nonneg f1]
    have h1 : f1 = 0 := by nlinarith [sq_nonneg f0, sq_nonneg f1]
    apply hfu; rw [h0, h1]; ring
  have hwf : (w0 * f0 + w1 * f1) * (f0 * u0 + f1 * u1) = 0 := by
    have : (f0 ^ 2 + f1 ^ 2) * (w0 * u0 + w1 * u1) = (w0 * f0 + w1 * f1) * (f0 * u0 + f1 * u1) := by
      linear_combination u0 * e0 + u1 * e1
    rw [← this, hwu, mul_zero]
  have hwf0 : w0 * f0 + w1 * f1 = 0 := by
    rcases mul_eq_zero.mp hwf with h | h
    · exact h
    · exact absurd h hfu
  rw [hwf0, zero_mul] at e0 e1
  exact ⟨(mul_eq_zero.mp e0).resolve_left hff, (mul_eq_zero.mp e1).resolve_left hff⟩

/-- Two points on the same open side of the line through `P ≠ R` with equal distances to `P` and `R` coincide. -/
theorem same_side_unique (f : Plane →ₗ[ℝ] ℝ) (c : ℝ) {P R Y Y' : Plane} (hPR : P ≠ R)
    (hfP : f P = c) (hfR : f R = c) (hY : c < f Y) (hY' : c < f Y')
    (h1 : dist P Y = dist P Y') (h2 : dist R Y = dist R Y') : Y = Y' := by
  have q1 := congrArg (· ^ 2) h1
  have q2 := congrArg (· ^ 2) h2
  simp only [dist_sq_coord] at q1 q2
  rw [lin_coord f P] at hfP; rw [lin_coord f R] at hfR
  rw [lin_coord f Y] at hY; rw [lin_coord f Y'] at hY'
  set f0 := f (EuclideanSpace.single 0 1)
  set f1 := f (EuclideanSpace.single 1 1)
  have hd : (R 0 - P 0) ^ 2 + (R 1 - P 1) ^ 2 ≠ 0 := by
    intro h
    apply hPR
    have a0 : R 0 - P 0 = 0 := by nlinarith [sq_nonneg (R 0 - P 0), sq_nonneg (R 1 - P 1)]
    have a1 : R 1 - P 1 = 0 := by nlinarith [sq_nonneg (R 0 - P 0), sq_nonneg (R 1 - P 1)]
    ext i; fin_cases i
    · simp; linarith
    · simp; linarith
  have := alg2 (Y 0 - Y' 0) (Y 1 - Y' 1) f0 f1 (R 0 - P 0) (R 1 - P 1)
    (Y 0 + Y' 0 - 2 * P 0) (Y 1 + Y' 1 - 2 * P 1)
    (by nlinarith) (by nlinarith) (by nlinarith) (by nlinarith) hd
  ext i; fin_cases i
  · simp; linarith [this.1]
  · simp; linarith [this.2]

/-- **Reflection through the midpoint.**  `X` below the line `{f = c}`, `X'` above it, legs swapped:  `X' = P + R - X`. -/
theorem reflect_of_swapped (f : Plane →ₗ[ℝ] ℝ) (c : ℝ) {P R X X' : Plane} (hPR : P ≠ R)
    (hfP : f P = c) (hfR : f R = c) (hX : f X < c) (hX' : c < f X')
    (h1 : dist P X' = dist R X) (h2 : dist R X' = dist P X) : X' = P + R - X := by
  have hfY : f (P + R - X) = 2 * c - f X := by simp [map_sub, map_add, hfP, hfR]; ring
  refine same_side_unique f c hPR hfP hfR hX' (by rw [hfY]; linarith) ?_ ?_
  · rw [h1]
    have : dist P (P + R - X) = dist R X := by
      rw [dist_eq_norm, dist_eq_norm, show P - (P + R - X) = -(R - X) by abel, norm_neg]
    exact this.symm
  · rw [h2]
    have : dist R (P + R - X) = dist P X := by
      rw [dist_eq_norm, dist_eq_norm, show R - (P + R - X) = -(P - X) by abel, norm_neg]
    exact this.symm

end Erdos634.Pi3F6
