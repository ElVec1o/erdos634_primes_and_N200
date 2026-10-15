import Mathlib.Geometry.Euclidean.Angle.Oriented.Affine
import Mathlib.Tactic

/-!
# What Mathlib gives towards `HasAngleSums` (Erdős #634)

`HasAngleSums` is the classical statement of the angle sums at a point of a dissection.  Mathlib has no sectors,
no angular measure and no winding number, but it has ORIENTED angles at a point in an oriented two-dimensional space
(`EuclideanGeometry.oangle`, notation `∡`), valued in `Real.Angle = ℝ / 2πℤ`, together with additivity `oangle_add`
and the cyclic form `oangle_add_cyc3`.  The statement

    "the angles of the tiles around an interior point sum to 2π"

splits into two halves of very different difficulty:

  (i)  MOD 2π, IT IS FREE. Oriented angles around a point telescope: going once around a cycle of
       rays returns to the start, so the sum of the oriented angles is `0` in `ℝ / 2πℤ`. For three
       rays this is `oangle_add_cyc3` verbatim (`three_ray_telescope` below); for four rays it is
       the same telescoping (`four_ray_telescope`).

  (ii) THE LIFT IS THE REAL CONTENT. To turn that into "the unsigned tile angles, each in (0,π),
       sum to exactly 2π" one needs that the tiles at the point occupy pairwise disjoint angular
       sectors in cyclic order which together cover all directions. That is a statement about the
       local structure of the dissection, not about angles.

No angular measure is built.  The route is measure theory throughout: areas of cones in a ball, never sectors or
winding numbers.  The chain is

      `SectorArea.volume_sector` / `Wedge.sector_eq_halfplanes`
        → `E2Join.volume_halfplane_wedge`, `E2Join.volume_wedge`   (a wedge has area θ/2)
        → `VertexSector.*`                                          (a tile's local angle at p)
        → `AngleSumDissection.Dissection.sum_localAngle_eq`, `Tri.localAngle_interior`
        → `Geometry.Dissection.hasAngleSums`, `PinPlumbing.pin_angle_sum_interior`.

`TangentCone.poly_inter_ball_eq_coneAt` and `AngleSumAssembled.angle_sum_interior` are a parallel proof of the same
reduction, not steps of this chain.  `TangentCone` reaches the unconditional form through
`TangentCone.exists_ball_poly_eq_coneAt`.
-/

open EuclideanGeometry

namespace Erdos634.AngleSumScope

variable {V : Type*} {P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P] [Fact (Module.finrank ℝ V = 2)] [Module.Oriented ℝ V (Fin 2)]

/-- **Three rays around a point telescope to zero.** This is the mod-2π half of "the angles around
an interior point sum to `2π`", for three tiles. -/
theorem three_ray_telescope (p p₁ p₂ p₃ : P) (h₁ : p₁ ≠ p) (h₂ : p₂ ≠ p) (h₃ : p₃ ≠ p) :
    ∡ p₁ p p₂ + ∡ p₂ p p₃ + ∡ p₃ p p₁ = 0 :=
  oangle_add_cyc3 h₁ h₂ h₃

/-- **Four rays.** The same telescoping, one step longer: the general `n`-ray statement is this
induction, and it needs nothing beyond `oangle_add`. -/
theorem four_ray_telescope (p p₁ p₂ p₃ p₄ : P)
    (h₁ : p₁ ≠ p) (h₂ : p₂ ≠ p) (h₃ : p₃ ≠ p) (h₄ : p₄ ≠ p) :
    ∡ p₁ p p₂ + ∡ p₂ p p₃ + ∡ p₃ p p₄ + ∡ p₄ p p₁ = 0 := by
  have h : ∡ p₁ p p₂ + ∡ p₂ p p₃ = ∡ p₁ p p₃ := oangle_add h₁ h₂ h₃
  calc ∡ p₁ p p₂ + ∡ p₂ p p₃ + ∡ p₃ p p₄ + ∡ p₄ p p₁
      = (∡ p₁ p p₂ + ∡ p₂ p p₃) + ∡ p₃ p p₄ + ∡ p₄ p p₁ := by ring
    _ = ∡ p₁ p p₃ + ∡ p₃ p p₄ + ∡ p₄ p p₁ := by rw [h]
    _ = 0 := oangle_add_cyc3 h₁ h₃ h₄

/-!
## The lift, via area rather than sectors

The lift need not use sector theory.  Near an interior point `p`, each
tile containing `p` agrees with the CONE over its angular sector at `p` inside a small enough ball,
and a cone is invariant under homothety about `p`. Mathlib supplies both halves of what that needs:

  · `MeasureTheory.Measure.addHaar_image_homothety` : scaling a set about a point multiplies its
    measure by `|r|^(dim)`, here `r²`;
  · `EuclideanSpace.volume_ball` : the measure of `B(p,r)`, here `π r²`;
  · `Dissection.aedisjoint` and `Dissection.volume_target` (in `Dissection.lean`):
    the tiles have almost-disjoint interiors and cover.

Writing `cᵢ = volume (coneᵢ ∩ B(p,1))`, homothety gives `volume (coneᵢ ∩ B(p,r)) = cᵢ r²`, while
disjointness and covering give `∑ᵢ volume (Tᵢ ∩ B(p,r)) = volume B(p,r) = π r²`. Hence `∑ᵢ cᵢ = π`,
and since the unit sector of angle `θ` has area `θ/2`, `∑ᵢ θᵢ = 2π`.

So `HasAngleSums` at interior points reduces to exactly two elementary statements:

  (A) each tile agrees with its cone at `p` inside some ball `B(p,ρ)`, `ρ > 0`;
  (B) the unit circular sector of angle `θ` has area `θ/2`.

Neither needs a theory of angular measure, and (A) is a statement about a convex polygon near one of
its points. The same computation at a boundary point gives `π`, and at a corner the corner angle.
-/

/-- **The CONCLUSION of the lift, not its hypothesis.** Warning, so that this is never used as an
assumption: the second conjunct below *is* the statement `∑ θᵢ = 2π`. This predicate does not
encode cyclic order, sector disjointness, or covering, since no clause here mentions the rays at all.
It records the shape of the target.  The unconditional statement is `Geometry.Dissection.hasAngleSums`
(`AngleSumDissection.lean`). -/
def UnsignedAnglesSumToTwoPi {n : ℕ} (unsigned : Fin n → ℝ) : Prop :=
  (∀ i, 0 < unsigned i ∧ unsigned i < Real.pi) ∧ (∑ i, unsigned i = 2 * Real.pi)

end Erdos634.AngleSumScope
