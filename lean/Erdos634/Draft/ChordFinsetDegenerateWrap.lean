import Erdos634.ChordFinsetDegenerate

namespace Erdos634.Draft.ChordFinsetDegenerateWrap
open Erdos634.Geometry Erdos634.ChordTraceReal

theorem wrap_hausdorff_segment_self (u : Plane) :
    (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane) (segment ℝ u u) = 0 :=
  hausdorff_segment_self u

theorem wrap_chord_decomposition_of_trivial_gap {N : ℕ} (D : Dissection N)
    (f : Plane →ₗ[ℝ] ℝ) (c : ℝ) (u : Plane) :
    (∑ e ∈ D.lineChain f c,
        (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane)
          ((D.tile e.1).edge e.2 ∩ segment ℝ u u))
      = (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane) (segment ℝ u u) :=
  chord_decomposition_of_trivial_gap D f c u

example : True := trivial
#print axioms wrap_chord_decomposition_of_trivial_gap

end Erdos634.Draft.ChordFinsetDegenerateWrap
