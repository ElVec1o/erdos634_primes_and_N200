import Erdos634.Tiling99Bridge

namespace Erdos634.Draft.Tiling99BridgeWrap
open Erdos634.Geometry Erdos634.Tiling99Bridge

theorem wrap_exists_dissection_99_mul_sq (m : ℕ) (hm : 0 < m) :
    ∃ E : CongruentDissection (99 * m ^ 2), E.model = pieceTri headI_mem_tiles :=
  exists_dissection_99_mul_sq m hm

example : True := trivial
#print axioms wrap_exists_dissection_99_mul_sq

end Erdos634.Draft.Tiling99BridgeWrap
