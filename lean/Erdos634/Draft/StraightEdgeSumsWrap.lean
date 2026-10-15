import Erdos634.StraightEdgeSums

namespace Erdos634.Draft.StraightEdgeSumsWrap
open Erdos634.Geometry MeasureTheory

theorem wrap_below_angle_sum_of_covering {N : ℕ} (D : Dissection N) (below : Finset (Fin N))
    (p : Plane) {r : ℝ} (hr : 0 < r) (g : Plane →ᵃ[ℝ] ℝ) (hL : g.linear ≠ 0) (hx : g p = 0)
    (hcontrib : ∀ i ∈ below, volume ((D.tile i).carrier ∩ Metric.ball p r)
        = ENNReal.ofReal ((D.tile i).localAngle p / 2 * r ^ 2))
    (hcov : (⋃ i ∈ below, ((D.tile i).carrier ∩ Metric.ball p r))
            = {y : Plane | 0 ≤ g y} ∩ Metric.ball p r) :
    ∑ i ∈ below, (D.tile i).localAngle p = Real.pi :=
  below_angle_sum_of_covering D below p hr g hL hx hcontrib hcov

example : True := trivial
#check @wrap_below_angle_sum_of_covering

end Erdos634.Draft.StraightEdgeSumsWrap
