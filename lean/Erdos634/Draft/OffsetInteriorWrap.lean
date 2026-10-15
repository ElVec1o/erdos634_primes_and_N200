import Erdos634.OffsetInterior

namespace Erdos634.Draft.OffsetInteriorWrap
open Erdos634.OffsetInterior

theorem wrap_apex_at_multiple (f j : ℤ) :
    j * (3 * f ^ 2 - 1) + j * (-(f ^ 2 - 1)) = 2 * f * (j * f) :=
  apex_at_multiple f j

example : True := trivial
#print axioms wrap_apex_at_multiple

end Erdos634.Draft.OffsetInteriorWrap
