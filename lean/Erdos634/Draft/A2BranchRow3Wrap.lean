import Erdos634.A2BranchRow3

namespace Erdos634.Draft.A2BranchRow3Wrap
open Erdos634.A2BranchRow3

/-- Gamma wedge cases: the only two solutions when `na + 2·ng = 2` and `nb + ng = 1`. -/
theorem wrap_gamma_wedge_cases (na nb ng : ℕ) (h1 : na + 2 * ng = 2) (h2 : nb + ng = 1) :
    (na = 2 ∧ nb = 1 ∧ ng = 0) ∨ (na = 0 ∧ nb = 0 ∧ ng = 1) :=
  gamma_wedge_cases na nb ng h1 h2

/-- With no straddler the fill is the mate. -/
theorem wrap_mate_forced (na nb ng : ℕ) (h1 : na + 2 * ng = 2) (h2 : nb + ng = 1)
    (no_straddler : ng = 0) : na = 2 ∧ nb = 1 :=
  mate_forced na nb ng h1 h2 no_straddler

/-- The b-filler dies at any straight junction. -/
theorem wrap_b_filler_dies (na nb ng : ℕ) (h1 : na + 2 * ng = 3) (h2 : nb + ng = 2) : ng ≤ 1 :=
  b_filler_dies na nb ng h1 h2

/-- The count that makes it work: f + 1 > f. -/
theorem wrap_endpoints_exceed_supply (f : ℕ) : f + 1 > f :=
  endpoints_exceed_supply f

example : True := trivial

#print axioms wrap_gamma_wedge_cases

end Erdos634.Draft.A2BranchRow3Wrap
