import Erdos634.ChordDecompositionThreeStraddlersFinal

namespace Erdos634.Draft.ChordDecompositionThreeStraddlersFinalWrap
open Erdos634.Geometry Erdos634.ChordTraceReal

theorem wrap_chord_decomposition_three_straddlers' {N : ℕ} (D : Dissection N)
    (f : Plane →ₗ[ℝ] ℝ) (hf : f ≠ 0) (c : ℝ)
    (hlo : ∃ i, f (D.target.pts i) < c) (hhi : ∃ j, c < f (D.target.pts j))
    {p q : Plane}
    (hp : p ∈ D.target.carrier ∩ {x | f x = c}) (hq : q ∈ D.target.carrier ∩ {x | f x = c})
    {m₁ m₂ m₃ : Fin N} (hm12 : m₁ ≠ m₂) (hm13 : m₁ ≠ m₃) (hm23 : m₂ ≠ m₃)
    {r₁ s₁ r₂ s₂ r₃ s₃ : Plane}
    (hpr₁ : p ≠ r₁) (hs₁r₂ : s₁ ≠ r₂) (hs₂r₃ : s₂ ≠ r₃) (hs₃q : s₃ ≠ q)
    (hr₁s₁ : r₁ ≠ s₁) (hr₂s₂ : r₂ ≠ s₂) (hs₁s₂ : s₁ ≠ s₂) (hs₂s₃ : s₂ ≠ s₃) (hr₃s₃ : r₃ ≠ s₃)
    (hr₁ : r₁ ∈ D.target.carrier ∩ {x | f x = c}) (hs₁ : s₁ ∈ D.target.carrier ∩ {x | f x = c})
    (hr₂ : r₂ ∈ D.target.carrier ∩ {x | f x = c}) (hs₂ : s₂ ∈ D.target.carrier ∩ {x | f x = c})
    (hr₃ : r₃ ∈ D.target.carrier ∩ {x | f x = c}) (hs₃ : s₃ ∈ D.target.carrier ∩ {x | f x = c})
    (hm₁trace : (D.tile m₁).carrier ∩ {x | f x = c} = segment ℝ r₁ s₁)
    (hm₂trace : (D.tile m₂).carrier ∩ {x | f x = c} = segment ℝ r₂ s₂)
    (hm₃trace : (D.tile m₃).carrier ∩ {x | f x = c} = segment ℝ r₃ s₃)
    (hws1 : Wbtw ℝ p s₁ q) (hwr1 : Wbtw ℝ p r₁ s₁)
    (hwr2 : Wbtw ℝ s₁ r₂ q) (hws2 : Wbtw ℝ r₂ s₂ q)
    (hwr3 : Wbtw ℝ s₂ r₃ s₃) (hwr3q : Wbtw ℝ r₃ s₃ q)
    (hw_r1s1r2 : Wbtw ℝ r₁ s₁ r₂) (hw_r2s2r3 : Wbtw ℝ r₂ s₂ r₃)
    (hunique : ∀ k : Fin N, k ≠ m₁ → k ≠ m₂ → k ≠ m₃ →
      ¬ ((∃ a, f ((D.tile k).pts a) < c) ∧ (∃ b, c < f ((D.tile k).pts b)))) :
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
  chord_decomposition_three_straddlers' D f hf c hlo hhi hp hq hm12 hm13 hm23
    hpr₁ hs₁r₂ hs₂r₃ hs₃q hr₁s₁ hr₂s₂ hs₁s₂ hs₂s₃ hr₃s₃
    hr₁ hs₁ hr₂ hs₂ hr₃ hs₃
    hm₁trace hm₂trace hm₃trace
    hws1 hwr1 hwr2 hws2 hwr3 hwr3q hw_r1s1r2 hw_r2s2r3 hunique

example : True := trivial
#print axioms wrap_chord_decomposition_three_straddlers'

end Erdos634.Draft.ChordDecompositionThreeStraddlersFinalWrap
