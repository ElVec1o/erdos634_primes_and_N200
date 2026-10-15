import Erdos634.Tiling44Scalene

namespace Erdos634.Draft.Tiling44ScaleneWrap
open Erdos634.TilePlacement

theorem wrap_tiling44_model_scalene :
    sideOpp Erdos634.Tiling44Bridge.dissection.model 0
      ≠ sideOpp Erdos634.Tiling44Bridge.dissection.model 1 ∧
    sideOpp Erdos634.Tiling44Bridge.dissection.model 0
      ≠ sideOpp Erdos634.Tiling44Bridge.dissection.model 2 ∧
    sideOpp Erdos634.Tiling44Bridge.dissection.model 1
      ≠ sideOpp Erdos634.Tiling44Bridge.dissection.model 2 :=
  _root_.tiling44_model_scalene

example : True := trivial
#print axioms wrap_tiling44_model_scalene

end Erdos634.Draft.Tiling44ScaleneWrap
