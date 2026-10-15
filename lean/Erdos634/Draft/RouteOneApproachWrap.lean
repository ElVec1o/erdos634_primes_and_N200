import Erdos634.RouteOneApproach

namespace Erdos634.Draft.RouteOneApproachWrap
open Erdos634.RouteOneApproach

theorem wrap_approach_witness :
    step 1 0 = 1 / 4 ∧ step 1 0 / (2 * (0 + 1 : ℝ)) = 1 / 8 ∧
      (1 / 8 : ℝ) ≤ (1 / (0 + 1 : ℝ)) * (1 / 4) ∧ (0 : ℝ) < 1 / 8 :=
  approach_witness

example : True := trivial
#print axioms wrap_approach_witness

end Erdos634.Draft.RouteOneApproachWrap
