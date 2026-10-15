import Erdos634.OrderForcing

/-!
# What the angle threshold is for: wrapper

Condition (P4) says that the uncovered region never acquires a corner sharper than the tile's own
sharpest angle α.  The comparison is with cos α = (2f²-1)/(2f²).  The uncovered region is not an
object of the Lean development, so only the arithmetic kernel is formalized:

1. **`anglethreshold_cos_alpha`**: cos α = (2f²-1)/(2f²) in cleared form (OrderForcing.cos_alpha_closed).
2. **`anglethreshold_cos_beta_gamma`**: cos β and cos γ in cleared form (OrderForcing.cos_beta_gamma_closed).

The condition (P4) itself (the convex corners of the uncovered region have angle ≥ α) is not
formalized, since the uncovered region is not.

No `sorry`; standard axioms only.
-/

namespace Erdos634.Draft.AngleThresholdWrap

open Erdos634.OrderForcing

/-- rem:anglethreshold arithmetic: cos α = (2f²-1)/(2f²), cleared form (ring identity). -/
theorem anglethreshold_cos_alpha (f : ℤ) :
    2 * f ^ 2 * ((f ^ 2 - 1) ^ 2 + (f ^ 2) ^ 2 - f ^ 2)
      = (2 * f ^ 2 - 1) * (2 * (f ^ 2 - 1) * f ^ 2) :=
  cos_alpha_closed f

/-- rem:anglethreshold: cos β and cos γ identities. -/
theorem anglethreshold_cos_beta_gamma (f : ℤ) :
    (2 * f ^ 3 * (f ^ 2 + (f ^ 2) ^ 2 - (f ^ 2 - 1) ^ 2) = (3 * f ^ 2 - 1) * (2 * f * f ^ 2))
    ∧ (2 * f * (f ^ 2 + (f ^ 2 - 1) ^ 2 - (f ^ 2) ^ 2) = -(2 * f * (f ^ 2 - 1)) + 0) :=
  cos_beta_gamma_closed f

#print axioms anglethreshold_cos_alpha
#print axioms anglethreshold_cos_beta_gamma

end Erdos634.Draft.AngleThresholdWrap
