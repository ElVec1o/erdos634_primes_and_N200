import Erdos634.Unsplittable

namespace Erdos634.Draft.UnsplittableWrap
open Erdos634.Unsplittable

theorem wrap_c_split {e f x y z : ℤ} (he : 1 ≤ e) (hef : e < f) (hcop : IsCoprime e f)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (heq : x * (e * f) + y * (f ^ 2 - e ^ 2) + z * f ^ 2 = f ^ 2) :
    (x = 0 ∧ y = 0 ∧ z = 1) ∨ (e = 1 ∧ x = f ∧ y = 0 ∧ z = 0) :=
  c_split he hef hcop hx hy hz heq

example : True := trivial
#print axioms wrap_c_split

end Erdos634.Draft.UnsplittableWrap
