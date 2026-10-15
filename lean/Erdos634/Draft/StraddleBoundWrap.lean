import Erdos634.StraddleBound

namespace Erdos634.Draft.StraddleBoundWrap
open Erdos634.StraddleBound

theorem wrap_chord_endpoints (f i : ℤ) :
    (f + i - f = i) ∧ (f + i - (i + 1) = f - 1) :=
  chord_endpoints f i

example : True := trivial
#check @wrap_chord_endpoints

end Erdos634.Draft.StraddleBoundWrap
