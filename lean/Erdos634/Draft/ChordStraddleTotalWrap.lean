import Erdos634.ChordStraddleTotal
namespace Erdos634.Draft.ChordStraddleTotalWrap
open Erdos634.Geometry Erdos634.ChordTraceReal

theorem wrap_hausdorffMeasure_one_subsingleton_eq_zero {s : Set Plane} (hs : s.Subsingleton) :
    (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane) s = 0 :=
  hausdorffMeasure_one_subsingleton_eq_zero hs

theorem wrap_straddle_total_eq_sum {N : ℕ} (D : Erdos634.Geometry.Dissection N)
    (f : Plane →ₗ[ℝ] ℝ) (c : ℝ) :
    (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane)
        (⋃ i ∈ straddlers D f c, (D.tile i).carrier ∩ {x | f x = c})
      = ∑ i ∈ straddlers D f c,
          (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane)
            ((D.tile i).carrier ∩ {x | f x = c}) :=
  straddle_total_eq_sum D f c

example : True := trivial
#print axioms straddle_total_eq_sum
end Erdos634.Draft.ChordStraddleTotalWrap
