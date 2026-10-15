import Erdos634.BaseBetaWalks

/-!
# Unique representation of k·b and the half-angle decomposition: arithmetic kernels

## Unique representation of k·b

For `1 ≤ k ≤ f−1`, the only representation of `k·b` as
`na·ef + nb·b + nc·f²` is `(na,nb,nc) = (0,k,0)`. Proved by mod-f reduction: `f ∣ nb−k`, and
the size bound `0 ≤ nb ≤ k` (from positivity of B and the length equation) forces `nb = k`;
the remainder vanishes. Uses `far_near_disjoint` (nc = 0 by disjointness) then coprimality.

## The angle (π−α)/2 decomposes only as α+β

A vertex figure filling `(π−α)/2` must be `{α,β}`: no other
combination of `{α,β,γ}` sums to `(π−α)/2`. Written via irrationality of α/π: the equations
`y + z = 1` and `2x + z + 1 = 3y` have the unique solution `(x,y,z) = (1,1,0)`.

Applying these to a real `CongruentDissection` needs the mismatch-ray / far-side geometry (for the first) or the
b-edge endpoint figure (for the second), which are not part of this file.

No sorry; standard axioms.
-/

namespace Erdos634.Draft.KbRepWrap

open Erdos634.BaseBetaWalks

/-- Unique representation of k·b: (na, nb, nc) = (0, k, 0) for 1 ≤ k ≤ f−1. -/
theorem kbrep_unique {e f k na nb nc B : ℕ}
    (hcop : Nat.Coprime e f) (hef : e < f) (he : 2 ≤ e)
    (hk1 : 1 ≤ k) (hk2 : k + 1 ≤ f) (hB : B + e ^ 2 = f ^ 2)
    (h : k * B = na * (e * f) + nb * B + nc * f ^ 2) :
    na = 0 ∧ nb = k ∧ nc = 0 :=
  kb_unique_rep e f k na nb nc B hcop hef he hk1 hk2 hB h

/-- The angle (π−α)/2 decomposes only as {α,β}: the only solution to y+z=1, 2x+z+1=3y is
    (x,y,z) = (1,1,0). -/
theorem halfangle_unique (x y z : ℕ) (h1 : y + z = 1) (h2 : 2 * x + z + 1 = 3 * y) :
    x = 1 ∧ y = 1 ∧ z = 0 :=
  halfpi_minus_alpha_unique x y z h1 h2

/-- Non-vacuity for kbrep: at (e,f,B) = (2,3,5), k=1: 1*5 = 0*6 + 1*5 + 0*9. -/
theorem kbrep_witness :
    (5 : ℕ) + 2 ^ 2 = 3 ^ 2 ∧ (1 : ℕ) * 5 = 0 * (2 * 3) + 1 * 5 + 0 * 3 ^ 2 := by norm_num

/-- Non-vacuity for halfangle: the unique solution (1,1,0) satisfies the equations. -/
theorem halfangle_witness :
    (1 : ℕ) + 0 = 1 ∧ 2 * 1 + 0 + 1 = 3 * 1 ∧ (1 : ℕ) = 1 ∧ (1 : ℕ) = 1 ∧ (0 : ℕ) = 0 := by
  norm_num

#print axioms kbrep_unique
#print axioms halfangle_unique

end Erdos634.Draft.KbRepWrap
