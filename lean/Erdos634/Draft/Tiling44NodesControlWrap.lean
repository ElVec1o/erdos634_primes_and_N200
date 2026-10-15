import Erdos634.Tiling44NodesControl

namespace Erdos634.Draft.Tiling44NodesControlWrap
open Erdos634.Geometry Erdos634.CertCoord Erdos634.Tiling44Bridge Erdos634.Tiling44Nodes
open Erdos634.Tiling44Control Erdos634.Tiling44NodesControl

theorem wrap_control_node_2 :
    (∃ j, j ∉ ([idx0, idx1] : List (Fin Tiling44.tiles.length)).toFinset ∧
      (dissection.tile j).carrier = T8.carrier) ∧
    (dissection.tile idx2).carrier = T8.carrier :=
  control_node_2

example : True := trivial
#print axioms wrap_control_node_2

end Erdos634.Draft.Tiling44NodesControlWrap
