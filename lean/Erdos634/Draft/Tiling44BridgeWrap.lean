import Erdos634.Tiling44Bridge

namespace Erdos634.Draft.Tiling44BridgeWrap
open Erdos634.Geometry Erdos634.Tiling44Bridge

theorem wrap_exists_dissection_44_mul_sq (m : ℕ) (hm : 0 < m) :
    ∃ E : CongruentDissection (44 * m ^ 2), E.model = pieceTri headI_mem_tiles :=
  exists_dissection_44_mul_sq m hm

example : True := trivial
#check @wrap_exists_dissection_44_mul_sq

end Erdos634.Draft.Tiling44BridgeWrap
