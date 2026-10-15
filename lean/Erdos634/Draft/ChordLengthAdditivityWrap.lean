import Erdos634.ChordLengthAdditivity

namespace Erdos634.Draft.ChordLengthAdditivityWrap
open Erdos634.Geometry Erdos634.ChordTraceReal

theorem wrap_hausdorff_segment_split {x y z : Plane} (hxy : y ∈ segment ℝ x z) :
    (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane) (segment ℝ x z)
      = (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane) (segment ℝ x y)
      + (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane) (segment ℝ y z) :=
  hausdorff_segment_split hxy

example : True := trivial
#print axioms wrap_hausdorff_segment_split

end Erdos634.Draft.ChordLengthAdditivityWrap
