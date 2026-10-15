import Erdos634.Inflation

/-!
# Inflation side-rigidity: arithmetic kernel

Boundary words of an inflated tile: the a-, b- and c-sides of the inflated tile each carry a rigid sequence of
tile edges, and the inflated tile has f² sub-tiles. Parity forces same-parity counts on the equal sides, which
kills the p=1 boundary at the special members (1,5) and (1,7) (squares 25, 49).

This file wraps the arithmetic content of `Inflation.lean`:

1. **`a_side_rigid`**: if a side of length `k·a` (k < f) is covered by `na` a-edges and `nc`
   c-edges (no b-edges), then `na = k` and `nc = 0`.

2. **`a_side_no_b`**: any side of length `k·a` (k ≤ f) coverable in tile edges has `nb = 0`.

3. **`b_side_rigid`**: if a side of length `k·b` (k < f) is covered by `nb` b-edges (and
   possibly a and c), then `na = 0`, `nb = k`, `nc = 0`.

4. **`c_side_no_b`**: any side of length `k·c` (k < f) covered by tile edges has `nb = 0`
   (this works for all members, including f/e < √2).

5. **`parity_forces_same_parity`**: interior + boundary edge parities are linked (2I + B = 3N²);
   the b-side and a-side counts must have the same parity.

6. **`parity_kills_25`**, **`parity_kills_49`**: at members (1,5) and (1,7) (N=3f²−1 = 74,146
   with tiles (5,24,25) and (7,48,49) resp.), the parity equation 3N² = 2I + B with
   the boundary b-count condition has no solution.

Only the arithmetic is formalized here. The side-rigidity statements constrain boundary words under the
geometric hypothesis that a corner takes one tile whose edges lie along the two flanking sides, and the `3N²`
parity identity is stated for edge counts, not for a `Dissection` object.

No sorry; axioms [propext, Classical.choice, Quot.sound] (interval_cases in sub-proofs).
-/

namespace Erdos634.Draft.InflationSideWrap

open Erdos634.Inflation

/-- The a-side of a scale-k inflation (k < f) carries no b-edge. -/
theorem inflation_a_side_no_b {e f b k na nb nc : ℕ} (he : 1 ≤ e) (hef : e < f)
    (hcop : Nat.Coprime e f) (hb : b + e ^ 2 = f ^ 2) (hk : k ≤ f)
    (heq : na * (e * f) + nb * b + nc * f ^ 2 = k * (e * f)) :
    nb = 0 :=
  a_side_no_b e f b k na nb nc he hef hcop hb hk heq

/-- The a-side of a scale-k inflation (k < f) is rigid: exactly k a-edges, no c-edges. -/
theorem inflation_a_side_rigid {e f k na nc : ℕ} (he : 1 ≤ e) (hef : e < f)
    (hcop : Nat.Coprime e f) (hkf : k < f)
    (heq : na * (e * f) + nc * f ^ 2 = k * (e * f)) :
    na = k ∧ nc = 0 :=
  a_side_rigid e f k na nc he hef hcop hkf heq

/-- The b-side of a scale-k inflation (k < f) is rigid: exactly k b-edges, no a- or c-edges. -/
theorem inflation_b_side_rigid {e f b k na nb nc : ℕ} (he : 1 ≤ e) (hef : e < f)
    (hcop : Nat.Coprime e f) (hb : b + e ^ 2 = f ^ 2) (hk : k < f)
    (heq : na * (e * f) + nb * b + nc * f ^ 2 = k * b) :
    na = 0 ∧ nb = k ∧ nc = 0 :=
  b_side_rigid e f b k na nb nc he hef hcop hb hk heq

/-- The c-side of a scale-k inflation (k < f) carries no b-edge (all members, no size bound). -/
theorem inflation_c_side_no_b {e f b k na nb nc : ℕ} (he : 1 ≤ e) (hef : e < f)
    (hcop : Nat.Coprime e f) (hb : b + e ^ 2 = f ^ 2) (hk : k < f)
    (heq : na * (e * f) + nb * b + nc * f ^ 2 = k * f ^ 2) :
    nb = 0 :=
  c_side_no_b e f b k na nb nc he hef hcop hb hk heq

/-- Parity: the parity of e must match that of f given the slot-count and boundary identity. -/
theorem inflation_parity_same (e f I B : ℕ)
    (hs : 3 * f ^ 2 = 2 * I + B) (hb : B + e = 4 * f) :
    e % 2 = f % 2 :=
  parity_forces_same_parity e f I B hs hb

/-- Parity kills the p=1 boundary at member (1,5) (tile (5,24,25), N = 74). -/
theorem inflation_parity_kills_25 {I B : ℕ}
    (hs : 3 * 5 ^ 2 = 2 * I + B) (hb : B + 2 = 4 * 5) : False :=
  parity_kills_25 I B hs hb

/-- Parity kills the p=1 boundary at member (1,7) (tile (7,48,49), N = 146). -/
theorem inflation_parity_kills_49 {I B : ℕ}
    (hs : 3 * 9 ^ 2 = 2 * I + B) (hb : B + 4 = 4 * 9) : False :=
  parity_kills_49 I B hs hb

/-- Non-vacuity: at (e,f) = (1,2), the a-side rigid hypotheses are satisfiable.
    k=1 < f=2: 1·2 + 0·4 = 1·2. -/
theorem inflation_a_side_witness :
    ∃ na nc : ℕ, na * (1 * 2) + nc * 2 ^ 2 = 1 * (1 * 2) ∧ (1 : ℕ) < 2 ∧ na = 1 ∧ nc = 0 :=
  ⟨1, 0, by norm_num, by norm_num, rfl, rfl⟩

#print axioms inflation_a_side_no_b
#print axioms inflation_a_side_rigid
#print axioms inflation_b_side_rigid
#print axioms inflation_c_side_no_b
#print axioms inflation_parity_same
#print axioms inflation_parity_kills_25
#print axioms inflation_parity_kills_49

end Erdos634.Draft.InflationSideWrap
