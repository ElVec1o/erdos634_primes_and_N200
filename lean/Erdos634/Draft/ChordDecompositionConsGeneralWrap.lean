import Erdos634.ChordDecompositionConsGeneral

namespace Erdos634.Draft.ChordDecompositionConsGeneralWrap
open Erdos634.Geometry Erdos634.ChordTraceReal

theorem wrap_chord_decomposition_cons' {N : ℕ} (D : Dissection N)
    (f : Plane →ₗ[ℝ] ℝ) (hf : f ≠ 0) (c : ℝ)
    (hlo : ∃ i, f (D.target.pts i) < c) (hhi : ∃ j, c < f (D.target.pts j))
    {p q r s : Plane}
    (hp : p ∈ D.target.carrier ∩ {x | f x = c}) (hr : r ∈ D.target.carrier ∩ {x | f x = c})
    (hwbtw1 : Wbtw ℝ p r s) (hwbtw2 : Wbtw ℝ p s q)
    (hgap : ∀ k : Fin N, ∀ y ∈ openSegment ℝ p r, y ∉ interior (D.tile k).carrier)
    (Trest : ENNReal)
    (hrest : (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane)
        (segment ℝ s q) = Trest) :
    (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane) (segment ℝ p q)
      = (∑ e ∈ D.lineChain f c,
            (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane)
              ((D.tile e.1).edge e.2 ∩ segment ℝ p r))
        + (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane) (segment ℝ r s)
        + Trest :=
  chord_decomposition_cons' D f hf c hlo hhi hp hr hwbtw1 hwbtw2 hgap Trest hrest

example : True := trivial
#print axioms wrap_chord_decomposition_cons'

end Erdos634.Draft.ChordDecompositionConsGeneralWrap
