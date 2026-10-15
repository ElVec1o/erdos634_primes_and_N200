import Erdos634.EscapeNoLanding

namespace Erdos634.Draft.EscapeNoLandingWrap

open Erdos634.EscapeNoLanding

theorem enl_admissible_no_a_block (f bp cp j : ℕ) (hf : 3 ≤ f)
    (hbp0 : 3 ≤ bp) (hbp1 : bp ≤ f)
    (hjb : j + f ≤ f + 2) (hblock : ∀ i, i < f → isAcfg bp cp (j + i)) : False :=
  admissible_no_a_block f bp cp j hf hbp0 hbp1 hjb hblock

theorem enl_admissible_no_landing (f B bp cp x y z j : ℕ) (hf : 3 ≤ f) (hB : B + 1 = f * f)
    (hbp0 : 3 ≤ bp) (hbp1 : bp ≤ f)
    (hspan : x * f + y * B + z * (B + 1) = B + 1) (hk : f ≤ x + y + z)
    (hfit : j + (x + y + z) ≤ f + 2)
    (hletters : ∀ i, i < x + y + z → isAcfg bp cp (j + i)) : False :=
  admissible_no_landing f B bp cp x y z j hf hB hbp0 hbp1 hspan hk hfit hletters

theorem enl_span_hypotheses_satisfiable (f B : ℕ) (hf : 3 ≤ f) (hB : B + 1 = f * f) :
    f * f + 0 * B + 0 * (B + 1) = B + 1 ∧ f ≤ f + 0 + 0 ∧ 0 + (f + 0 + 0) ≤ f + 2 :=
  span_hypotheses_satisfiable f B hf hB

example : True := trivial

#print axioms enl_admissible_no_landing
#print axioms enl_span_hypotheses_satisfiable

end Erdos634.Draft.EscapeNoLandingWrap
