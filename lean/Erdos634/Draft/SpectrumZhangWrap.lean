import Erdos634.SpectrumZhang

namespace Erdos634.Draft.SpectrumZhangWrap
open Erdos634.SpectrumZhang

theorem wrap_zhang_admissible
    (a b c d e m : ℤ) (hc : c ^ 2 = a ^ 2 + a * b + b ^ 2) (hb : b = d * e ^ 2) :
    3 * a * (d * e * (e * m)) = (c + a - b) * ((c + b - a) * m) ∧
    3 * a * (d * e * (e * m)) = (c + b - a) * ((c + a - b) * m) ∧
    ((((c + b - a) * m : ℤ)) : ZMod 2) = ((d * (e * m) ^ 2 * (a + 2 * b) : ℤ) : ZMod 2) ∧
    ((((c + a - b) * m : ℤ)) : ZMod 2) = ((d * (e * m) ^ 2 * (a + 2 * b) : ℤ) : ZMod 2) :=
  zhang_admissible a b c d e m hc hb

example : True := trivial
#check @wrap_zhang_admissible

end Erdos634.Draft.SpectrumZhangWrap
