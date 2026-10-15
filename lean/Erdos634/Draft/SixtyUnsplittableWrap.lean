import Erdos634.SixtyUnsplittable

namespace Erdos634.Draft.SixtyUnsplittableWrap
open Erdos634.SixtyUnsplittable

theorem wrap_b_unsplittable (T : Triple) (x z : ℤ) (hx : 0 ≤ x) (hz : 0 ≤ z)
    (hsum : 2 ≤ x + z) (hb : T.b = x * T.a + z * T.c) : T.a ∣ T.b :=
  b_unsplittable T x z hx hz hsum hb

example : True := trivial
#print axioms wrap_b_unsplittable

end Erdos634.Draft.SixtyUnsplittableWrap
