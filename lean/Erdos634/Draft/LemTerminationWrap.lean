import Erdos634.OrderForcing

/-!
# Termination is one condition: arithmetic kernel

The termination of a chain is characterised by a single
arithmetic condition: if two consecutive lengths m and m+1 are both achievable as
base-β walk sums (with e=1, f≥3), then f²≤m+1. This closes the boundary/interior
dichotomy at the end of a chain run.

The arithmetic is proved in `OrderForcing.lean`:
- **`consecutive_gap`**: for f≥3, if x₁f+y₁(f²−1)+z₁f²=m and x₂f+y₂(f²−1)+z₂f²=m+1
  then f²≤m+1.

That termination is "boundary or interior" for real chain configurations is a placement statement, not part of
this file.

No sorry; standard axioms.
-/

namespace Erdos634.Draft.LemTerminationWrap

open Erdos634.OrderForcing

/-- Consecutive gap: two adjacent achievable lengths force f²≤m+1. -/
theorem termination_consecutive_gap {f m x1 y1 z1 x2 y2 z2 : ℕ} (hf : 3 ≤ f)
    (h1 : x1 * f + y1 * (f * f - 1) + z1 * (f * f) = m)
    (h2 : x2 * f + y2 * (f * f - 1) + z2 * (f * f) = m + 1) :
    f * f ≤ m + 1 :=
  consecutive_gap hf h1 h2

/-- Non-vacuity: at f=3, m=8: 0·3+1·8+0·9=8 and 0·3+0·8+1·9=9, giving 9≤9. -/
theorem termination_consecutive_gap_witness :
    (3 : ℕ) ≤ 3 ∧ 0 * 3 + 1 * (3 * 3 - 1) + 0 * (3 * 3) = 8 ∧
    0 * 3 + 0 * (3 * 3 - 1) + 1 * (3 * 3) = 9 ∧ 3 * 3 ≤ 9 := by norm_num

#print axioms termination_consecutive_gap

end Erdos634.Draft.LemTerminationWrap
