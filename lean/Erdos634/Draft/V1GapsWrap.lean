import Erdos634.V1Gaps

/-!
# Three arithmetic exclusions in the numerical semigroup ⟨ef, f²−e², f²⟩

Key arithmetic facts in `V1Gaps.lean` (coprime e<f, f>2e):

1. **`N1_overrun_stub_gap`**: x·ef + y·b + z·f² = f²−2e² has no solution.
   (The whole-edge closure of the chord-extension [T,W] does not exist.)

2. **`N3_c_rep_unique`**: for e≥2, x·ef + y·b + z·f² = f² forces (x,y,z)=(0,0,1).
   (The unique representation of c is (0,0,1) for e≥2; fails at e=1.)

3. **`N2_master_through_kill`**: no through-edge configuration σ < b < σ+L with
   σ+L+x·a = 2b has a solution.

All three bottom out in f∣e² or f∣2e² against gcd(e,f)=1, f>2e.

The geometric inputs (pin_angle_sum, through-exclusivity, blocked-end run equation) are used elsewhere;
only the three arithmetic cores are proved here.  0 sorry, standard axioms.
-/

namespace Erdos634.Draft.V1GapsWrap

open Erdos634.V1Gaps

/-- N1 kill: f²−2e² ∉ ⟨ef, b, f²⟩ for coprime (e,f), f>2e. -/
theorem v1gaps_N1 (e f b d x y z : ℕ) (he : 1 ≤ e) (hef : 2 * e < f)
    (hco : Nat.Coprime e f) (hb : b + e * e = f * f) (hd : d + 2 * (e * e) = f * f)
    (h : x * (e * f) + y * b + z * (f * f) = d) : False :=
  N1_overrun_stub_gap e f b d x y z he hef hco hb hd h

/-- N3 uniqueness: for e≥2, the only representation of f² is (0,0,1). -/
theorem v1gaps_N3 (e f b x y z : ℕ) (he : 2 ≤ e) (hef : 2 * e < f)
    (hco : Nat.Coprime e f) (hb : b + e * e = f * f)
    (h : x * (e * f) + y * b + z * (f * f) = f * f) :
    x = 0 ∧ y = 0 ∧ z = 1 :=
  N3_c_rep_unique e f b x y z he hef hco hb h

/-- N2 master through-kill: no through-edge closure σ+L+x·a=2b with σ<b<σ+L. -/
theorem v1gaps_N2 (e f b p q r L x : ℕ) (he : 1 ≤ e) (hef : 2 * e < f)
    (hco : Nat.Coprime e f) (hb : b + e * e = f * f)
    (hL : L = e * f ∨ L = b ∨ L = f * f)
    (hs1 : p * (e * f) + q * b + r * (f * f) < b)
    (hs2 : b < p * (e * f) + q * b + r * (f * f) + L)
    (h : p * (e * f) + q * b + r * (f * f) + L + x * (e * f) = 2 * b) : False :=
  N2_master_through_kill e f b p q r L x he hef hco hb hL hs1 hs2 h

/-- Non-vacuity N1 witness: (e,f)=(3,7): b+9=49 so b=40, d+18=49 so d=31;
    x=0,y=0,z=0 gives LHS=0≠31 but we just need the type-checks. -/
theorem v1gaps_N1_witness : (1 : ℕ) ≤ 3 ∧ 2 * 3 < 7 ∧ Nat.Coprime 3 7 ∧
    (40 : ℕ) + 3 * 3 = 7 * 7 ∧ (31 : ℕ) + 2 * (3 * 3) = 7 * 7 := by
  norm_num [Nat.Coprime]

/-- Non-vacuity N3 witness: (e,f)=(2,5): b+4=25 so b=21;
    (0,0,1): 0·10+0·21+1·25=25 ✓. -/
theorem v1gaps_N3_witness : (2 : ℕ) ≤ 2 ∧ 2 * 2 < 5 ∧ Nat.Coprime 2 5 ∧
    (21 : ℕ) + 2 * 2 = 5 * 5 ∧ (0 : ℕ) * (2*5) + 0 * 21 + 1 * (5*5) = 5 * 5 := by
  norm_num [Nat.Coprime]

#print axioms v1gaps_N1
#print axioms v1gaps_N3
#print axioms v1gaps_N2

end Erdos634.Draft.V1GapsWrap
