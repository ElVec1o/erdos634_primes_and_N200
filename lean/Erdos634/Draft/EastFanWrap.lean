import Erdos634.OrderForcing

/-!
# East fan at the fork: arithmetic kernel (wrapper)

At the fork point, the east fan is forced. The junction arithmetic
is: at a straight figure with angle sum `3α + 2β = 2π`, the vertex figures are either `{3α,2β,0γ}`
or `{1α,1β,1γ}`, with at most one `γ`.

The arithmetic content is in `OrderForcing.lean`:

1. **`straight_junction_cases`**: given `na + 2·ng = 3` and `nb + ng = 2`, exactly two solutions:
   `(na,nb,ng) = (3,2,0)` or `(1,1,1)`. This is the complete vertex-figure enumeration at a
   straight (3α+2β) junction.

2. **`straight_junction_gamma_bound`**: at a straight junction, `ng ≤ 1`. Combined with the two
   cases above: no two γ-corners meet at the fork's east fan junction.

Only the junction arithmetic is formalized here, not the placement statement about the tile configuration at the fork.

No sorry, axioms [] (pure omega).
-/

namespace Erdos634.Draft.EastFanWrap

open Erdos634.OrderForcing

/-- At a straight (3α+2β) junction, exactly two vertex figures occur: {3α,2β} or {1α,1β,1γ}. -/
theorem east_fan_junction_cases (na nb ng : ℕ)
    (h1 : na + 2 * ng = 3) (h2 : nb + ng = 2) :
    (na = 3 ∧ nb = 2 ∧ ng = 0) ∨ (na = 1 ∧ nb = 1 ∧ ng = 1) :=
  straight_junction_cases na nb ng h1 h2

/-- At a straight junction, at most one γ is present. -/
theorem east_fan_gamma_le_one (na nb ng : ℕ)
    (h1 : na + 2 * ng = 3) (h2 : nb + ng = 2) : ng ≤ 1 :=
  straight_junction_gamma_bound na nb ng h1 h2

/-- Non-vacuity: both cases are satisfiable. -/
theorem east_fan_witness_no_gamma :
    (3 : ℕ) + 2 * 0 = 3 ∧ (2 : ℕ) + 0 = 2 ∧ (3 : ℕ) = 3 ∧ (2 : ℕ) = 2 ∧ (0 : ℕ) = 0 := by
  norm_num

theorem east_fan_witness_with_gamma :
    (1 : ℕ) + 2 * 1 = 3 ∧ (1 : ℕ) + 1 = 2 ∧ (1 : ℕ) = 1 ∧ (1 : ℕ) = 1 ∧ (1 : ℕ) = 1 := by
  norm_num

#print axioms east_fan_junction_cases
#print axioms east_fan_gamma_le_one

end Erdos634.Draft.EastFanWrap
