import Erdos634.ThickEFminus1Probe

namespace Erdos634.Draft.ThickEFminus1ProbeWrap
open Erdos634.ThickEFminus1Probe
open Real

theorem wrap_two_gamma_gt_pi {α β γ : ℝ} (hsum : 3 * α + 2 * β = π) (hγ : γ = 2 * α + β)
    (hα : 0 < α) : π < 2 * γ :=
  two_gamma_gt_pi hsum hγ hα

example : True := trivial
#print axioms wrap_two_gamma_gt_pi

end Erdos634.Draft.ThickEFminus1ProbeWrap
