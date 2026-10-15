import Erdos634.BaseBetaWalks

/-!
# Alignment of the mismatch ray: arithmetic kernel

The mismatch ray is determined as follows: the far side is `b^f`, the near side has a unique
representation, and the two sets of junctions are disjoint.  The alignment arithmetic has three
components:

1. **`far_near_disjoint`**: for `1 ≤ k ≤ f−1`, `nc ≥ 1` implies `k·B ≠ na·ef + nb·B + nc·f²`.
   This is the far/near disjointness: no c-edge can appear in a k·b-length side segment.

2. **`b_not_dvd_fsq`**: for `e ≥ 2`, `B ∤ f²`. So no far junction lands on the vertex V = f².
   The proof: `B ∣ f²` implies `B ∣ e²` (by coprimality), hence `B ∣ gcd(f²,e²) = 1`, impossible
   since `B ≥ 5`.

3. **`far_is_bpow`**: for `e ≥ 2`, `nb ≥ 1` and `f·B = na·ef + nb·B + nc·f²` implies
   `(na,nb,nc) = (0,f,0)`. The far side is exactly `f` b-edges.

Only the arithmetic is formalized: the "mismatch ray" and its far/near sides have no
`Dissection`-level definition, and the geometric interpretation (that the ray hits V = f² from
outside) is a placement statement.

No `sorry`; standard axioms only.
-/

namespace Erdos634.Draft.AlignWrap

open Erdos634.BaseBetaWalks

/-- Far and near junctions are disjoint: no c-edge in a k·b segment for 1 ≤ k ≤ f−1. -/
theorem align_far_near_disjoint {e f k na nb nc B : ℕ}
    (hcop : Nat.Coprime e f) (hef : e < f)
    (hk1 : 1 ≤ k) (hk2 : k + 1 ≤ f) (hB : B + e ^ 2 = f ^ 2) (hnc : 1 ≤ nc) :
    k * B ≠ na * (e * f) + nb * B + nc * f ^ 2 :=
  far_near_disjoint e f k na nb nc B hcop hef hk1 hk2 hB hnc

/-- b does not divide f² at any e ≥ 2 member. -/
theorem align_b_not_dvd_fsq {e f B : ℕ}
    (hcop : Nat.Coprime e f) (hef : e < f) (he : 2 ≤ e) (hB : B + e ^ 2 = f ^ 2) :
    ¬ B ∣ f ^ 2 :=
  b_not_dvd_fsq e f B hcop hef he hB

/-- The far side is b^f: the unique representation of f·b with nb ≥ 1. -/
theorem align_far_is_bpow {e f na nb nc B : ℕ}
    (hcop : Nat.Coprime e f) (hef : e < f) (he : 2 ≤ e)
    (hB : B + e ^ 2 = f ^ 2) (hb1 : 1 ≤ nb)
    (h : f * B = na * (e * f) + nb * B + nc * f ^ 2) :
    na = 0 ∧ nb = f ∧ nc = 0 :=
  far_is_bpow e f na nb nc B hcop hef he hB hb1 h

/-- Non-vacuity: at (e,f,B) = (2,3,5): B + e² = f², 2 ≥ 2, far_is_bpow holds for nb=3. -/
theorem align_witness_b_not_dvd : ¬ (5 : ℕ) ∣ 9 := by norm_num

theorem align_witness_far_is_bpow :
    (5 : ℕ) + 2 ^ 2 = 3 ^ 2 ∧ (1 : ℕ) ≤ 3 ∧
    3 * 5 = 0 * (2 * 3) + 3 * 5 + 0 * 3 ^ 2 := by norm_num

#print axioms align_far_near_disjoint
#print axioms align_b_not_dvd_fsq
#print axioms align_far_is_bpow

end Erdos634.Draft.AlignWrap
