import Erdos634.ConeScaling

/-!
# ConeScaling: angle sum wrapper
Key results:
- `angle_sum_of_cones_X`: almost-disjoint cones covering `B(p,1)` with sectors of area `θᵢ/2` satisfy `∑ θᵢ = 2π`.
No sorry, standard axioms.
-/

namespace Erdos634.Draft.ConeScalingWrap
open Erdos634.ConeScaling MeasureTheory Set Metric

/-- Wrap: finitely many almost-disjoint measurable pieces covering the unit ball,
each of area `θᵢ/2`, satisfy `∑ θᵢ = 2π`. -/
theorem angle_sum_of_cones_X {n : ℕ} (p : Plane) (C : Fin n → Set Plane) (θ : Fin n → ℝ)
    (hmeas : ∀ i, MeasurableSet (C i ∩ ball p 1))
    (hdisj : Pairwise (Function.onFun (AEDisjoint volume) (fun i => C i ∩ ball p 1)))
    (hcover : ⋃ i, (C i ∩ ball p 1) = ball p 1)
    (harea : ∀ i, volume (C i ∩ ball p 1) = ENNReal.ofReal (θ i / 2))
    (hθ : ∀ i, 0 ≤ θ i)
    (hball : volume (ball p (1:ℝ)) = ENNReal.ofReal Real.pi) :
    ∑ i, θ i = 2 * Real.pi :=
  angle_sum_of_cones p C θ hmeas hdisj hcover harea hθ hball

-- Non-vacuity: the unit ball has positive measure (uses that π > 0)
example : (0 : ℝ) < Real.pi := Real.pi_pos

#print axioms angle_sum_of_cones_X
end Erdos634.Draft.ConeScalingWrap
