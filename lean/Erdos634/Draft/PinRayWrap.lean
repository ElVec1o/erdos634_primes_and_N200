import Erdos634.PinRay

namespace Erdos634.Draft.PinRayWrap
open Erdos634.PinRay

theorem wrap_exit_not_integral_member (f p T : ℤ) (hf : 2 ≤ f) (hp1 : 1 ≤ p) (hp2 : p ≤ f - 1)
    (h : (3 * f ^ 2 - 1) * T = f ^ 3 * ((3 * f ^ 2 - 1) - p * f)) : False :=
  exit_not_integral_member f p T hf hp1 hp2 h

example : True := trivial
#print axioms wrap_exit_not_integral_member

end Erdos634.Draft.PinRayWrap
