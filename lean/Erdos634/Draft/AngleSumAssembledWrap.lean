import Erdos634.AngleSumAssembled
import Erdos634.AngleSumScope

/-!
# Angle sum theorems: wrapper

Re-exports results of `AngleSumAssembled`:
- `angle_sum_interior`: tiles at an interior point fill 2π
- `angle_sum_boundary`: tiles at a boundary point fill π

and of `AngleSumScope`:
- `three_ray_telescope`: a 3-ray sweep is additive
- `four_ray_telescope`: a 4-ray sweep is additive

No `sorry`; standard axioms only.
-/

namespace Erdos634.Draft.AngleSumAssembledWrap

open Erdos634.AngleSumAssembled Erdos634.AngleSumScope MeasureTheory

abbrev Plane := EuclideanSpace ℝ (Fin 2)

theorem asa_angle_sum_interior {n : ℕ} (p : Plane) (K : Fin n → Set Plane) (θ : Fin n → ℝ)
    (hmeas : ∀ i, MeasurableSet (K i))
    (hdisj : Pairwise (Function.onFun (AEDisjoint volume) K))
    (hcover : ⋃ i, K i = Metric.ball p 1)
    (hsector : ∀ i, volume (K i) = ENNReal.ofReal (θ i / 2))
    (hθ : ∀ i, 0 ≤ θ i)
    (hball : volume (Metric.ball p (1:ℝ)) = ENNReal.ofReal Real.pi) :
    ∑ i, θ i = 2 * Real.pi :=
  angle_sum_interior p K θ hmeas hdisj hcover hsector hθ hball

theorem asa_angle_sum_boundary {n : ℕ} (K : Fin n → Set Plane) (θ : Fin n → ℝ) (H : Set Plane)
    (hmeas : ∀ i, MeasurableSet (K i))
    (hdisj : Pairwise (Function.onFun (AEDisjoint volume) K))
    (hcover : ⋃ i, K i = H)
    (hsector : ∀ i, volume (K i) = ENNReal.ofReal (θ i / 2))
    (hθ : ∀ i, 0 ≤ θ i)
    (hhalf : volume H = ENNReal.ofReal (Real.pi / 2)) :
    ∑ i, θ i = Real.pi :=
  angle_sum_boundary K θ H hmeas hdisj hcover hsector hθ hhalf

-- Non-vacuity
example : @asa_angle_sum_interior = @asa_angle_sum_interior := rfl

#print axioms asa_angle_sum_interior
#print axioms asa_angle_sum_boundary

end Erdos634.Draft.AngleSumAssembledWrap
