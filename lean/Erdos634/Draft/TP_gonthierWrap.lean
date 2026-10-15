import Erdos634.TP_gonthier

namespace Erdos634.Draft.TP_gonthierWrap
open Erdos634.TPGonthier

theorem wrap_witnesses :
    0 < nD ∧ dface 0 = 0 ∧ dface (ag 0) ≠ dface 0 ∧ darts.length = 162
      ∧ 3 * faceCyc.length < darts.length :=
  witnesses

example : True := trivial
#check @witnesses

end Erdos634.Draft.TP_gonthierWrap
