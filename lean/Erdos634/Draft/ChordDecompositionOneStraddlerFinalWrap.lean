import Erdos634.ChordDecompositionOneStraddlerFinal

namespace Erdos634.Draft.ChordDecompositionOneStraddlerFinalWrap
open Erdos634.Geometry Erdos634.ChordTraceReal

theorem wrap_chord_decomposition_one_straddler' {N : ℕ} (D : Dissection N)
    (f : Plane →ₗ[ℝ] ℝ) (hf : f ≠ 0) (c : ℝ)
    (hlo : ∃ i, f (D.target.pts i) < c) (hhi : ∃ j, c < f (D.target.pts j))
    {p q : Plane}
    (hp : p ∈ D.target.carrier ∩ {x | f x = c}) (hq : q ∈ D.target.carrier ∩ {x | f x = c})
    {m : Fin N} {r s : Plane} (hpr : p ≠ r) (hsq : s ≠ q)
    (hr : r ∈ D.target.carrier ∩ {x | f x = c}) (hs : s ∈ D.target.carrier ∩ {x | f x = c})
    (hmtrace : (D.tile m).carrier ∩ {x | f x = c} = segment ℝ r s)
    (hwbtw1 : Wbtw ℝ p r q) (hwbtw2 : Wbtw ℝ r s q)
    (hunique : ∀ k : Fin N, k ≠ m →
      ¬ ((∃ a, f ((D.tile k).pts a) < c) ∧ (∃ b, c < f ((D.tile k).pts b)))) :
    (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane) (segment ℝ p q)
      = (∑ e ∈ D.lineChain f c,
            (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane)
              ((D.tile e.1).edge e.2 ∩ segment ℝ p r))
        + (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane) (segment ℝ r s)
        + (∑ e ∈ D.lineChain f c,
              (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane)
                ((D.tile e.1).edge e.2 ∩ segment ℝ s q)) :=
  chord_decomposition_one_straddler' D f hf c hlo hhi hp hq hpr hsq hr hs hmtrace hwbtw1 hwbtw2 hunique

example : True := trivial
#print axioms wrap_chord_decomposition_one_straddler'

end Erdos634.Draft.ChordDecompositionOneStraddlerFinalWrap
