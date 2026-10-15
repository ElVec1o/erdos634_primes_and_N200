import Erdos634.ChordDecompositionNoStraddle

namespace Erdos634.Draft.ChordDecompositionNoStraddleWrap
open Erdos634.Geometry Erdos634.ChordTraceReal

theorem wrap_chord_decomposition_of_no_straddlers {N : ℕ} (D : Dissection N)
    (f : Plane →ₗ[ℝ] ℝ) (hf : f ≠ 0) (c : ℝ)
    (hlo : ∃ i, f (D.target.pts i) < c) (hhi : ∃ j, c < f (D.target.pts j))
    {p q : Plane} (hpq : p ≠ q)
    (hp : p ∈ D.target.carrier ∩ {x | f x = c}) (hq : q ∈ D.target.carrier ∩ {x | f x = c})
    (hseg : D.target.carrier ∩ {x | f x = c} = segment ℝ p q)
    (hnostraddle : ∀ i : Fin N,
      ¬ ((∃ a, f ((D.tile i).pts a) < c) ∧ (∃ b, c < f ((D.tile i).pts b)))) :
    ∑ e ∈ D.lineChain f c,
        (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane)
          ((D.tile e.1).edge e.2 ∩ segment ℝ p q)
      = (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane)
          (segment ℝ p q) :=
  chord_decomposition_of_no_straddlers D f hf c hlo hhi hpq hp hq hseg hnostraddle

example : True := trivial
#print axioms wrap_chord_decomposition_of_no_straddlers

end Erdos634.Draft.ChordDecompositionNoStraddleWrap
