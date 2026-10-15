import Erdos634.ChordDecompositionThreeStraddlers

namespace Erdos634.Draft.ChordDecompositionThreeStraddlersWrap
open Erdos634.Geometry Erdos634.ChordTraceReal

theorem wrap_chord_decomposition_three_straddlers {N : ℕ} (D : Dissection N)
    (f : Plane →ₗ[ℝ] ℝ) (hf : f ≠ 0) (c : ℝ)
    (hlo : ∃ i, f (D.target.pts i) < c) (hhi : ∃ j, c < f (D.target.pts j))
    {p q r₁ s₁ r₂ s₂ r₃ s₃ : Plane}
    (hpr₁ : p ≠ r₁) (hs₁r₂ : s₁ ≠ r₂) (hs₂r₃ : s₂ ≠ r₃) (hs₃q : s₃ ≠ q)
    (hp : p ∈ D.target.carrier ∩ {x | f x = c}) (hq : q ∈ D.target.carrier ∩ {x | f x = c})
    (hr₁ : r₁ ∈ D.target.carrier ∩ {x | f x = c}) (hs₁ : s₁ ∈ D.target.carrier ∩ {x | f x = c})
    (hr₂ : r₂ ∈ D.target.carrier ∩ {x | f x = c}) (hs₂ : s₂ ∈ D.target.carrier ∩ {x | f x = c})
    (hr₃ : r₃ ∈ D.target.carrier ∩ {x | f x = c}) (hs₃ : s₃ ∈ D.target.carrier ∩ {x | f x = c})
    (hws1 : Wbtw ℝ p s₁ q) (hwr1 : Wbtw ℝ p r₁ s₁)
    (hwr2 : Wbtw ℝ s₁ r₂ q) (hws2 : Wbtw ℝ r₂ s₂ q)
    (hws3 : Wbtw ℝ s₂ s₃ q) (hwr3 : Wbtw ℝ s₂ r₃ s₃)
    (hgap1 : ∀ k : Fin N, ∀ y ∈ openSegment ℝ p r₁, y ∉ interior (D.tile k).carrier)
    (hgap2 : ∀ k : Fin N, ∀ y ∈ openSegment ℝ s₁ r₂, y ∉ interior (D.tile k).carrier)
    (hgap3 : ∀ k : Fin N, ∀ y ∈ openSegment ℝ s₂ r₃, y ∉ interior (D.tile k).carrier)
    (hgap4 : ∀ k : Fin N, ∀ y ∈ openSegment ℝ s₃ q, y ∉ interior (D.tile k).carrier) :
    (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane) (segment ℝ p q)
      = (∑ e ∈ D.lineChain f c,
            (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane)
              ((D.tile e.1).edge e.2 ∩ segment ℝ p r₁))
        + (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane)
            (segment ℝ r₁ s₁)
        + (∑ e ∈ D.lineChain f c,
              (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane)
                ((D.tile e.1).edge e.2 ∩ segment ℝ s₁ r₂))
        + (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane)
            (segment ℝ r₂ s₂)
        + (∑ e ∈ D.lineChain f c,
              (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane)
                ((D.tile e.1).edge e.2 ∩ segment ℝ s₂ r₃))
        + (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane)
            (segment ℝ r₃ s₃)
        + (∑ e ∈ D.lineChain f c,
              (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane)
                ((D.tile e.1).edge e.2 ∩ segment ℝ s₃ q)) :=
  chord_decomposition_three_straddlers D f hf c hlo hhi hpr₁ hs₁r₂ hs₂r₃ hs₃q
    hp hq hr₁ hs₁ hr₂ hs₂ hr₃ hs₃ hws1 hwr1 hwr2 hws2 hws3 hwr3 hgap1 hgap2 hgap3 hgap4

example : True := trivial
#print axioms wrap_chord_decomposition_three_straddlers

end Erdos634.Draft.ChordDecompositionThreeStraddlersWrap
