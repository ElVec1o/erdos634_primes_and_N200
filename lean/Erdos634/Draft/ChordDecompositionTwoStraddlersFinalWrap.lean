import Erdos634.ChordDecompositionTwoStraddlersFinal

namespace Erdos634.Draft.ChordDecompositionTwoStraddlersFinalWrap
open Erdos634.Geometry Erdos634.ChordTraceReal

theorem wrap_chord_decomposition_two_straddlers' {N : ℕ} (D : Dissection N)
    (f : Plane →ₗ[ℝ] ℝ) (hf : f ≠ 0) (c : ℝ)
    (hlo : ∃ i, f (D.target.pts i) < c) (hhi : ∃ j, c < f (D.target.pts j))
    {p q : Plane}
    (hp : p ∈ D.target.carrier ∩ {x | f x = c}) (hq : q ∈ D.target.carrier ∩ {x | f x = c})
    {m₁ m₂ : Fin N} (hm : m₁ ≠ m₂)
    {r₁ s₁ r₂ s₂ : Plane} (hpr₁ : p ≠ r₁) (hs₁r₂ : s₁ ≠ r₂) (hs₂q : s₂ ≠ q)
    (hr₁s₁ : r₁ ≠ s₁) (hs₁s₂ : s₁ ≠ s₂)
    (hr₁ : r₁ ∈ D.target.carrier ∩ {x | f x = c}) (hs₁ : s₁ ∈ D.target.carrier ∩ {x | f x = c})
    (hr₂ : r₂ ∈ D.target.carrier ∩ {x | f x = c}) (hs₂ : s₂ ∈ D.target.carrier ∩ {x | f x = c})
    (hm₁trace : (D.tile m₁).carrier ∩ {x | f x = c} = segment ℝ r₁ s₁)
    (hm₂trace : (D.tile m₂).carrier ∩ {x | f x = c} = segment ℝ r₂ s₂)
    (hws1 : Wbtw ℝ p s₁ q) (hwr1 : Wbtw ℝ p r₁ s₁)
    (hwr2 : Wbtw ℝ s₁ r₂ q) (hws2 : Wbtw ℝ r₂ s₂ q)
    (hw_r1s1r2 : Wbtw ℝ r₁ s₁ r₂)
    (hunique : ∀ k : Fin N, k ≠ m₁ → k ≠ m₂ →
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
                ((D.tile e.1).edge e.2 ∩ segment ℝ s₂ q)) :=
  chord_decomposition_two_straddlers' D f hf c hlo hhi hp hq hm hpr₁ hs₁r₂ hs₂q hr₁s₁ hs₁s₂
    hr₁ hs₁ hr₂ hs₂ hm₁trace hm₂trace hws1 hwr1 hwr2 hws2 hw_r1s1r2 hunique

example : True := trivial
#print axioms wrap_chord_decomposition_two_straddlers'

end Erdos634.Draft.ChordDecompositionTwoStraddlersFinalWrap
