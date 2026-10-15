import Erdos634.VertexSector

namespace Erdos634.Draft.VertexSectorWrap
open Erdos634.Geometry MeasureTheory

theorem wrap_volume_ball_plane (x : Plane) {r : ℝ} (hr : 0 ≤ r) :
    volume (Metric.ball x r) = ENNReal.ofReal (Real.pi * r ^ 2) :=
  volume_ball_plane x hr

example : True := trivial
#print axioms wrap_volume_ball_plane

end Erdos634.Draft.VertexSectorWrap
