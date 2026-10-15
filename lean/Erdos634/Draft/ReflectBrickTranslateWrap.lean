import Erdos634.ReflectBrickTranslate

namespace Erdos634.Draft.ReflectBrickTranslateWrap
open Erdos634.Geometry Erdos634.AreaDet Erdos634.DissectionMap Erdos634.TranslateDissection

theorem wrap_carrier_union_reflectThroughEdge1_translate (T : Tri) (v : Plane) :
    (mapTri (transEquiv v).toAffineEquiv T).carrier
      ∪ (reflectThroughEdge (mapTri (transEquiv v).toAffineEquiv T) 1).carrier
      = (fun x => v + x) '' (T.carrier ∪ (reflectThroughEdge T 1).carrier) :=
  carrier_union_reflectThroughEdge1_translate T v

example : True := trivial
#print axioms wrap_carrier_union_reflectThroughEdge1_translate

end Erdos634.Draft.ReflectBrickTranslateWrap
