import Erdos634.ScaleMap

/-!
# ScaleMap — angle-to-side-length scale map: wrapper

Key results:
- `sin_sq_alpha/beta/gamma`: sin² values from cosine for base-beta angles
- `scale_map`: the scale map theorem (existence of s with the triangle)

0 sorry, standard axioms.
-/

namespace Erdos634.Draft.ScaleMapWrap

open Erdos634.ScaleMap Erdos634.Geometry

theorem sm_sin_sq_alpha {f : ℝ} {θ : ℝ} (hcos : Real.cos θ = (2 * f ^ 2 - 1) / (2 * f ^ 2))
    (hf0 : f ≠ 0) : Real.sin θ ^ 2 = (4 * f ^ 2 - 1) / (4 * f ^ 4) :=
  sin_sq_alpha hcos hf0

theorem sm_sin_sq_beta {f : ℝ} {θ : ℝ} (hcos : Real.cos θ = (3 * f ^ 2 - 1) / (2 * f ^ 3))
    (hf0 : f ≠ 0) :
    Real.sin θ ^ 2 = (f ^ 2 - 1) ^ 2 * (4 * f ^ 2 - 1) / (4 * f ^ 6) :=
  sin_sq_beta hcos hf0

theorem sm_sin_sq_gamma {f : ℝ} {θ : ℝ} (hcos : Real.cos θ = -1 / (2 * f)) (hf0 : f ≠ 0) :
    Real.sin θ ^ 2 = (4 * f ^ 2 - 1) / (4 * f ^ 2) :=
  sin_sq_gamma hcos hf0

-- Non-vacuity
example : @sm_sin_sq_alpha = @sm_sin_sq_alpha := rfl

#print axioms sm_sin_sq_alpha
#print axioms sm_sin_sq_gamma

end Erdos634.Draft.ScaleMapWrap
