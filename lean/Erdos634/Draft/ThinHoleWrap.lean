import Erdos634.ThinHole

namespace Erdos634.Draft.ThinHoleWrap
open Erdos634.ThinHole

theorem wrap_rep_unique (p e1 f1 e2 f2 : ℤ) (hp : Prime p)
    (h1 : 3 * f1 ^ 2 - e1 ^ 2 = p) (h2 : 3 * f2 ^ 2 - e2 ^ 2 = p)
    (he1 : 1 ≤ e1) (hlt1 : e1 < f1) (hc1 : IsCoprime e1 f1)
    (he2 : 1 ≤ e2) (hlt2 : e2 < f2) (hc2 : IsCoprime e2 f2) :
    e1 = e2 ∧ f1 = f2 :=
  rep_unique p e1 f1 e2 f2 hp h1 h2 he1 hlt1 hc1 he2 hlt2 hc2

example : True := trivial
#print axioms wrap_rep_unique

end Erdos634.Draft.ThinHoleWrap
