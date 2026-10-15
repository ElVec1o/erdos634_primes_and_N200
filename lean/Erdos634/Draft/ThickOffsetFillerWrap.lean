import Erdos634.ThickOffsetFiller

namespace Erdos634.Draft.ThickOffsetFillerWrap
open Erdos634.ThickOffsetFiller
open Erdos634.Geometry Erdos634.CertCoord Erdos634.BaseBetaTargetCoord
open Erdos634.ThickJunctionCoords Erdos634.ThickWedgeGram

theorem wrap_far_end_not_clamped_by_boundary : 6 * Real.sqrt 2 < height 2 3 :=
  far_end_not_clamped_by_boundary

example : True := trivial
#print axioms wrap_far_end_not_clamped_by_boundary

end Erdos634.Draft.ThickOffsetFillerWrap
