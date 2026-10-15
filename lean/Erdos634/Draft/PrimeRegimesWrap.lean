import Erdos634.PrimeRegimes

namespace Erdos634.Draft.PrimeRegimesWrap
open Erdos634.PrimeRegimes

theorem wrap_wedge_fill_forced_everywhere (na nb ng : ℕ)
    (h1 : na + 2 * ng = 1) (h2 : nb + ng = 0) : na = 1 ∧ nb = 0 ∧ ng = 0 :=
  wedge_fill_forced_everywhere na nb ng h1 h2

example : True := trivial
#print axioms wrap_wedge_fill_forced_everywhere

end Erdos634.Draft.PrimeRegimesWrap
