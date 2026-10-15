import Erdos634.ChordBetweennessDisjointFar
namespace Erdos634.Draft.ChordBetweennessDisjointFarWrap
open Erdos634.Geometry Erdos634.ChordTraceReal

theorem wrap_openSegment_disjoint_segment_of_wbtw_far {p r u v : Plane}
    (hpr : p ≠ r) (hru : r ≠ u)
    (hpru : Wbtw ℝ p r u) (hruv : Wbtw ℝ r u v) :
    Disjoint (openSegment ℝ p r) (segment ℝ u v) :=
  openSegment_disjoint_segment_of_wbtw_far hpr hru hpru hruv

example : True := trivial
#print axioms wrap_openSegment_disjoint_segment_of_wbtw_far
end Erdos634.Draft.ChordBetweennessDisjointFarWrap
