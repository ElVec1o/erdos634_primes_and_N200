import Erdos634.ChordBetweennessDisjoint
namespace Erdos634.Draft.ChordBetweennessDisjointWrap
open Erdos634.Geometry Erdos634.ChordTraceReal

theorem wrap_openSegment_disjoint_segment_of_wbtw {p r s : Plane}
    (hpr : p ≠ r) (hprs : Wbtw ℝ p r s) :
    Disjoint (openSegment ℝ p r) (segment ℝ r s) :=
  openSegment_disjoint_segment_of_wbtw hpr hprs

example : True := trivial
#print axioms wrap_openSegment_disjoint_segment_of_wbtw
end Erdos634.Draft.ChordBetweennessDisjointWrap
