import Erdos634.ReflectBrick

namespace Erdos634.Draft.ReflectBrickWrap
open Erdos634.Geometry Erdos634.AreaDet

theorem wrap_carrier_union_reflectThroughEdge1 (T : Tri) :
    T.carrier ∪ (reflectThroughEdge T 1).carrier = placeMap T '' stdSquare :=
  carrier_union_reflectThroughEdge1 T

example : True := trivial
#print axioms wrap_carrier_union_reflectThroughEdge1

end Erdos634.Draft.ReflectBrickWrap
