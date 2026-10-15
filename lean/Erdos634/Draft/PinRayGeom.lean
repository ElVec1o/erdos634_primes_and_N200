import Erdos634.Draft.ColumnLinesGeom

/-!
# The pin ray leaves through the right side at distance `f³(L − x)/L`

The pin-buffer argument uses a ray from a base point
`(x, 0)` of the target, parallel to the left side, which leaves the target through the
right side at distance `T = f³(N₀ − p f)/N₀` (`N₀ = 3f² − 1`, `x = p f`, `e = 1`).  The
non-integrality of `T` is `PinRay.exit_not_integral`.

* `pin_ray_exit` : in the coordinates of `baseBetaTarget e f`, for `0 ≤ x ≤ L`, the point
  `(x, 0) + s·(apex − origin)` with `s = (L − x)/L` lies on the right side, and its distance from
  `(x, 0)` is `f³·s`.
* `pin_ray_exit_e1` : the case `e = 1`, `x = p f`: the distance is `f³(N₀ − p f)/N₀`.

No statement here is about a tiling.  Standard axioms, no `sorry`.
-/

namespace Erdos634.Draft.PinRayGeom

open Erdos634 Erdos634.Geometry Erdos634.CertCoord Erdos634.BaseBetaTargetCoord
open Erdos634.Draft.ColumnLinesGeom

theorem pin_ray_exit {e f : ℝ} (he : 0 < e) (hef : e < f) {x : ℝ} (hx0 : 0 ≤ x)
    (hxL : x ≤ baseLen e f) :
    mkPt x 0 + ((baseLen e f - x) / baseLen e f) •
        ((baseBetaTarget e f he hef).pts 2 - (baseBetaTarget e f he hef).pts 0)
      ∈ segment ℝ ((baseBetaTarget e f he hef).pts 1) ((baseBetaTarget e f he hef).pts 2) ∧
    dist (mkPt x 0) (mkPt x 0 + ((baseLen e f - x) / baseLen e f) •
        ((baseBetaTarget e f he hef).pts 2 - (baseBetaTarget e f he hef).pts 0))
      = f ^ 3 * ((baseLen e f - x) / baseLen e f) := by
  have hL := baseLen_pos he hef
  have hf : 0 < f := lt_trans he hef
  set s : ℝ := (baseLen e f - x) / baseLen e f with hs
  have hs0 : 0 ≤ s := div_nonneg (by linarith) hL.le
  have hs1 : s ≤ 1 := by rw [hs, div_le_one hL]; linarith
  have hsL : s * baseLen e f = baseLen e f - x := by rw [hs]; field_simp
  constructor
  · refine ⟨1 - s, s, by linarith, hs0, by ring, ?_⟩
    apply plane_ext
    · simp
      nlinarith [hsL]
    · simp
  · rw [dist_eq_norm]
    have : mkPt x 0 - (mkPt x 0 + s •
        ((baseBetaTarget e f he hef).pts 2 - (baseBetaTarget e f he hef).pts 0))
        = -(s • ((baseBetaTarget e f he hef).pts 2 - (baseBetaTarget e f he hef).pts 0)) := by
      abel
    rw [this, norm_neg, norm_smul, Real.norm_of_nonneg hs0, ← dist_eq_norm, dist_comm,
      baseBetaTarget_dist_leg₀ he hef]
    ring

/-- The case of the remark: `e = 1`, the pin at `x = p f`, `N₀ = 3f² − 1`. -/
theorem pin_ray_exit_e1 {f : ℝ} (hf : 1 < f) {p : ℝ} (hp0 : 0 ≤ p) (hp : p * f ≤ 3 * f ^ 2 - 1) :
    dist (mkPt (p * f) 0) (mkPt (p * f) 0 + ((3 * f ^ 2 - 1 - p * f) / (3 * f ^ 2 - 1)) •
        ((baseBetaTarget 1 f one_pos hf).pts 2 - (baseBetaTarget 1 f one_pos hf).pts 0))
      = f ^ 3 * (3 * f ^ 2 - 1 - p * f) / (3 * f ^ 2 - 1) := by
  have hL : baseLen 1 f = 3 * f ^ 2 - 1 := by unfold baseLen Nq; ring
  have hf0 : (0:ℝ) < f := by linarith
  have h := (pin_ray_exit (e := 1) one_pos hf (x := p * f) (by positivity) (by rw [hL]; exact hp)).2
  rw [hL] at h
  rw [h]; ring

end Erdos634.Draft.PinRayGeom
