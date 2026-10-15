import Erdos634.StraddlerApex

namespace Erdos634.Draft.StraddlerApexWrap
open Erdos634.StraddlerApex

theorem wrap_residue_is_gap {f x y z : ℕ} (hf : 3 ≤ f)
    (h : x * f + y * (f * f - 1) + z * (f * f) = f * f - 2) : False :=
  residue_is_gap hf h

example : True := trivial
#check @wrap_residue_is_gap

end Erdos634.Draft.StraddlerApexWrap
