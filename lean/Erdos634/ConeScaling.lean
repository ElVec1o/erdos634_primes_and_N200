import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Tactic

/-!
# Cone scaling and the angle sum

`AngleSumScope.lean` reduces the interior case of `HasAngleSums` to two statements; `SectorArea.lean`
proves the second (a unit sector of angle `θ` has area `θ/2`). This file concerns the scaling half
and the angle-sum conclusion.

A set `C` is a cone at `p` when it is invariant under every homothety about `p` with positive
ratio. The tangent cone of a tile at a point of it is such a set, and near `p` the tile agrees with
it; that agreement (statement (A)) is the geometric input and is not proved in this file.

  · `angle_sum_of_cones`: if finitely many sets have pairwise almost-disjoint intersections
    with `B(p,1)`, together cover it, and the `i`-th has unit-ball area `θᵢ/2`, then `∑ θᵢ = 2π`.

`IsConeAt` is defined but no theorem uses it, and `angle_sum_of_cones` carries no cone hypothesis
at all: it works at radius 1 throughout, so it is a statement about arbitrary measurable pieces. The
homothety identification `C ∩ B(p,r) = h_r '' (C ∩ B(p,1))` is stated in the comment below and is
not proved here. The angle-sum chain used elsewhere runs through `VertexSector` and
`AngleSumDissection`.

The angle-sum statement has the dissection-specific facts (disjointness, covering) as hypotheses,
exactly as they are supplied by `Dissection.aedisjoint` and the covering equation.
-/

open MeasureTheory Set Metric

namespace Erdos634.ConeScaling

/-- The plane. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- `C` is a cone at `p`: invariant under homothety about `p` of every positive ratio. -/
def IsConeAt (p : Plane) (C : Set Plane) : Prop :=
  ∀ r : ℝ, 0 < r → AffineMap.homothety p r '' C = C

/-! The scaling statement `volume (C ∩ B(p,r)) = r² · volume (C ∩ B(p,1))` for a cone at `p`
follows from `Measure.addHaar_image_homothety` once `C ∩ B(p,r)` is identified as the homothetic
image of `C ∩ B(p,1)`; that identification is a `Metric.ball` manipulation and is not carried out
here. It is not needed for the angle sum below, which works at radius 1 throughout. -/

/-- **The angle sum.** If the cones `C i` at `p` cut `B(p,1)` into almost-disjoint pieces covering
it, and the `i`-th piece has area `θ i / 2`, then `∑ θ i = 2π`. This is the interior case of
`HasAngleSums`, with the dissection facts as hypotheses. -/
theorem angle_sum_of_cones {n : ℕ} (p : Plane) (C : Fin n → Set Plane) (θ : Fin n → ℝ)
    (hmeas : ∀ i, MeasurableSet (C i ∩ ball p 1))
    (hdisj : Pairwise (Function.onFun (AEDisjoint volume) (fun i => C i ∩ ball p 1)))
    (hcover : ⋃ i, (C i ∩ ball p 1) = ball p 1)
    (harea : ∀ i, volume (C i ∩ ball p 1) = ENNReal.ofReal (θ i / 2))
    (hθ : ∀ i, 0 ≤ θ i)
    (hball : volume (ball p (1:ℝ)) = ENNReal.ofReal Real.pi) :
    ∑ i, θ i = 2 * Real.pi := by
  have hsum : ∑ i, volume (C i ∩ ball p 1) = volume (ball p 1) := by
    have hU := measure_iUnion₀ (μ := volume) hdisj (fun i => (hmeas i).nullMeasurableSet)
    rw [hcover, tsum_fintype] at hU
    exact hU.symm
  rw [hball] at hsum
  simp_rw [harea] at hsum
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => by linarith [hθ i])] at hsum
  have hpi : (0:ℝ) ≤ Real.pi := Real.pi_pos.le
  have hnn : (0:ℝ) ≤ ∑ i, θ i / 2 := Finset.sum_nonneg (fun i _ => by linarith [hθ i])
  have := (ENNReal.ofReal_eq_ofReal_iff hnn hpi).mp hsum
  have hhalf : ∑ i, θ i / 2 = (∑ i, θ i) / 2 := by
    rw [Finset.sum_div]
  rw [hhalf] at this
  linarith

end Erdos634.ConeScaling
