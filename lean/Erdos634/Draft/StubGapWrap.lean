import Erdos634.StubGap

namespace Erdos634.Draft.StubGapWrap
open Erdos634.StubGap

theorem wrap_stub_gap (e f x y z : ℤ) (he : 1 ≤ e) (hef : e < f) (hcop : IsCoprime e f)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    x * (e * f) + y * (f ^ 2 - e ^ 2) + z * f ^ 2 ≠ |e * f - (f ^ 2 - e ^ 2)| :=
  stub_gap e f x y z he hef hcop hx hy hz

example : True := trivial
#check @wrap_stub_gap

end Erdos634.Draft.StubGapWrap
