import Erdos634.BaseBetaWalks

/-!
# Pierce lemma and second rung: arithmetic kernels

`BaseBetaWalks.lean` contains the three arithmetic declarations used in the proofs of
the pierce lemma and the second rung.

## Pierce lemma, arithmetic content

* `apex_leftover_nonrepresentable`: the apex leftover e² is not representable as
  n_a·ef + n_b·b + n_c·f² for any n_a,n_b,n_c ≥ 0 when b + e² = f².
* `pierced_corner_types`: the two vertex-figure systems consistent with the corner constraint
  are exactly {3α,β} (x=3,y=1,z=0) and {α,γ} (x=1,y=0,z=1).

## Second rung, arithmetic content

* `far_near_disjoint`: the far junction at k·b (1 ≤ k ≤ f−1) cannot coincide with a
  near-side walk sum n_a·ef + n_b·b + n_c·f² that has n_c ≥ 1.
* `b_not_dvd_fsq`: b does not divide f², so no far junction reaches f².
* `far_is_bpow`: the only representation of f·b with n_b ≥ 1 is (0, f, 0), i.e. the far side is b^f.

That these arithmetic constraints apply to real tiles in a real `CongruentDissection` is a
placement statement and is not part of this file.

Standard axioms, no `sorry`.
-/

namespace Erdos634.Draft.PierceRungWrap

open Erdos634.BaseBetaWalks

/-- Bundle the two-theorem arithmetic content of thm:pierce. -/
theorem pierce_arithmetic (e f na nb nc B x y z : ℕ)
    (he : 1 ≤ e) (hef : e < f) (hcop : Nat.Coprime e f) (hB : B + e ^ 2 = f ^ 2)
    (hfig : y + z = 1 ∧ 2 * x + z = 3 * y + 3) :
    na * (e * f) + nb * B + nc * f ^ 2 ≠ e ^ 2 ∧
    ((x = 3 ∧ y = 1 ∧ z = 0) ∨ (x = 1 ∧ y = 0 ∧ z = 1)) :=
  ⟨apex_leftover_nonrepresentable e f na nb nc B he hef hcop hB,
   pierced_corner_types x y z hfig.1 hfig.2⟩

/-- Bundle the three-theorem arithmetic content of prop:rung2. -/
theorem rung2_arithmetic (e f k na nb nc B : ℕ)
    (hcop : Nat.Coprime e f) (hef : e < f) (he : 2 ≤ e)
    (hk1 : 1 ≤ k) (hk2 : k + 1 ≤ f) (hB : B + e ^ 2 = f ^ 2) (hnc : 1 ≤ nc) :
    k * B ≠ na * (e * f) + nb * B + nc * f ^ 2 ∧
    ¬ B ∣ f ^ 2 :=
  ⟨far_near_disjoint e f k na nb nc B hcop hef hk1 hk2 hB hnc,
   b_not_dvd_fsq e f B hcop hef he hB⟩

/-- Non-vacuity for pierce_arithmetic: (e,f) = (1,3), B = 8, figure {α,γ} (x=1,y=0,z=1). -/
theorem pierce_witness : ∃ e f na nb nc B x y z : ℕ,
    1 ≤ e ∧ e < f ∧ Nat.Coprime e f ∧ B + e ^ 2 = f ^ 2 ∧
    (y + z = 1 ∧ 2 * x + z = 3 * y + 3) ∧
    na * (e * f) + nb * B + nc * f ^ 2 ≠ e ^ 2 ∧
    ((x = 3 ∧ y = 1 ∧ z = 0) ∨ (x = 1 ∧ y = 0 ∧ z = 1)) :=
  ⟨1, 3, 0, 0, 0, 8, 1, 0, 1,
   by norm_num, by norm_num, by decide, by norm_num,
   ⟨by norm_num, by norm_num⟩,
   by norm_num, Or.inr ⟨rfl, rfl, rfl⟩⟩

/-- Non-vacuity for rung2_arithmetic: (e,f) = (2,3), B = 5, k = 1, na=0, nb=0, nc=1. -/
theorem rung2_witness : ∃ e f k na nb nc B : ℕ,
    Nat.Coprime e f ∧ e < f ∧ 2 ≤ e ∧ 1 ≤ k ∧ k + 1 ≤ f ∧ B + e ^ 2 = f ^ 2 ∧ 1 ≤ nc ∧
    k * B ≠ na * (e * f) + nb * B + nc * f ^ 2 ∧ ¬ B ∣ f ^ 2 :=
  ⟨2, 3, 1, 0, 0, 1, 5,
   by decide, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
   by norm_num, by norm_num⟩

#print axioms pierce_arithmetic
#print axioms rung2_arithmetic

end Erdos634.Draft.PierceRungWrap
