import Erdos634.FloorDependsOnJPos

namespace Erdos634.Draft.FloorDependsOnJPosWrap
open Erdos634.FloorDependsOnJPos

theorem wrap_floor_drops_iff {e f : ℤ} (hf : 0 < f) :
    f * (e * f) < f * (f ^ 2 - e ^ 2) ↔ e * f < f ^ 2 - e ^ 2 :=
  floor_drops_iff hf

example : True := trivial
#print axioms wrap_floor_drops_iff

end Erdos634.Draft.FloorDependsOnJPosWrap
