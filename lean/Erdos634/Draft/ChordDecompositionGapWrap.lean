import Erdos634.ChordDecompositionGap

namespace Erdos634.Draft.ChordDecompositionGapWrap
open Erdos634.Geometry Erdos634.ChordTraceReal

theorem wrap_chord_decomposition_of_gap {N : ℕ} (D : Dissection N)
    (f : Plane →ₗ[ℝ] ℝ) (hf : f ≠ 0) (c : ℝ)
    (hlo : ∃ i, f (D.target.pts i) < c) (hhi : ∃ j, c < f (D.target.pts j))
    {u₁ u₂ : Plane} (hu : u₁ ≠ u₂)
    (h1 : u₁ ∈ D.target.carrier ∩ {x | f x = c}) (h2 : u₂ ∈ D.target.carrier ∩ {x | f x = c})
    (hgapstraddle : ∀ k : Fin N, ∀ y ∈ openSegment ℝ u₁ u₂, y ∉ interior (D.tile k).carrier) :
    ∑ e ∈ D.lineChain f c,
        (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane)
          ((D.tile e.1).edge e.2 ∩ segment ℝ u₁ u₂)
      = (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane)
          (segment ℝ u₁ u₂) :=
  chord_decomposition_of_gap D f hf c hlo hhi hu h1 h2 hgapstraddle

example : True := trivial
#print axioms wrap_chord_decomposition_of_gap

end Erdos634.Draft.ChordDecompositionGapWrap
