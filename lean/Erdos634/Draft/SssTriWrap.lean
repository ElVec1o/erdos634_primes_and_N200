import Erdos634.SssTri

namespace Erdos634.Draft.SssTriWrap
open Erdos634.SssTri Erdos634.Geometry

theorem wrap_dist12 (p q r h : ℝ) (hr : r ≠ 0) (hp : 0 ≤ p)
    (hh : h ^ 2 = q ^ 2 - (xCoord p q r) ^ 2) :
    dist (sssPts p q r h 1) (sssPts p q r h 2) = p :=
  dist12 p q r h hr hp hh

example : True := trivial
#check @wrap_dist12

end Erdos634.Draft.SssTriWrap
