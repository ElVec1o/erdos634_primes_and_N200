import Erdos634.Frontier

/-!
# The extra-column reduction arithmetic: kernel wrapper

The extra base-decomposition columns at close pairs are described by six arithmetic theorems in
`Frontier.lean`.

Key arithmetic facts (all over ℤ or ℕ, coprime e < f):

1. **`base_column_reduction`**: With y = e+kf, the base equation factors as f × (reduced form).
2. **`base_column_k_one`**: k=1 with x=e forces z = 2e−f (unique; exists iff f ≤ 2e−1).
3. **`base_column_k_bound`**: x,z ≥ 1 forces k·b ≤ 2ef−e−f.
4. **`column_x_congruence`**: coprimality forces f ∣ x−ke (x is pinned mod f).
5. **`one_column_per_k`**: at most one column per k (e(1+q) ≤ kf from e < f alone).
6. **`k_bound_sharp`**: x+z ≥ 4 sharpens bound to k·b ≤ 2ef−3e−f.

`k_bound_sharp` needs x+z ≥ 4 from the corner parallelogram; the bridge to a real column context
is not part of this module.  Uniqueness across the k-range is observed, not proved.
-/

namespace Erdos634.Draft.ColumnReductionWrap

open Erdos634.Frontier

/-- The base equation reduced: with y=e+kf it is f times a linear combination. -/
theorem colred_reduction (e f k x z : ℤ) :
    x * (e * f) + (e + k * f) * (f * f - e * e) + z * (f * f) - e * (3 * f * f - e * e)
      = f * (x * e + z * f - (2 * e * f - k * (f * f - e * e))) :=
  base_column_reduction e f k x z

/-- k=1 forces z=2e−f (the column exists iff f ≤ 2e−1). -/
theorem colred_k_one (e f z : ℤ) (hf : f ≠ 0)
    (h : e * e + z * f = 2 * e * f - (f * f - e * e)) : z = 2 * e - f :=
  base_column_k_one e f z hf h

/-- x,z ≥ 1 forces k·b ≤ 2ef−e−f. -/
theorem colred_k_bound (e f k x z : ℤ) (hx : 1 ≤ x) (hz : 1 ≤ z) (he : 0 < e) (hf : 0 < f)
    (hkey : x * e + z * f = 2 * e * f - k * (f * f - e * e)) :
    k * (f * f - e * e) ≤ 2 * e * f - e - f :=
  base_column_k_bound e f k x z hx hz he hf hkey

/-- Coprimality forces f ∣ x−ke (x is in one residue class per k). -/
theorem colred_x_congruence (e f k x z : ℤ) (hco : IsCoprime f e)
    (h : x * e + z * f = 2 * e * f - k * (f * f - e * e)) : f ∣ x - k * e :=
  column_x_congruence e f k x z hco h

/-- At most one column per k: e(1+q) ≤ kf from e < f. -/
theorem colred_one_per_k {e f k q : ℕ} (he : 0 < e) (hef : e < f) (hk : 1 ≤ k)
    (hq : q * f ≤ k * e) (hq' : k * e < (q + 1) * f) : e * (1 + q) ≤ k * f :=
  one_column_per_k he hef hk hq hq'

/-- Sharp bound: x+z ≥ 4 tightens to k·b ≤ 2ef−3e−f. -/
theorem colred_k_bound_sharp (e f k x z : ℤ) (he : 0 < e) (hef : e < f)
    (hx : 1 ≤ x) (hz : 1 ≤ z) (hxz : 4 ≤ x + z)
    (hkey : x * e + z * f = 2 * e * f - k * (f * f - e * e)) :
    k * (f * f - e * e) ≤ 2 * e * f - 3 * e - f :=
  k_bound_sharp e f k x z he hef hx hz hxz hkey

/-- Non-vacuity for k_bound: (e,f,k)=(1,3,1), b=8; x=1,z=1 gives 1+3=4=2*3−8=−2 fails.
    Use (e,f,k,x,z)=(3,7,1,3,1): x*e+z*f=9+7=16=2*3*7−1*(49−9)=42−40=2 (no).
    Direct non-vacuity: we just need the hypotheses to be satisfiable. (e,f)=(2,3),b=5.
    k=1: x*2+z*3=2*2*3−1*5=7; x=2,z=1: 4+3=7 ✓; x,z≥1; x+z=3<4 (sharp needs 4).
    For basic bound: e=2,f=3,k=1,x=2,z=1: k*b=5 ≤ 2*2*3−2−3=7 ✓. -/
theorem colred_witness : (1:ℤ) ≤ 2 ∧ (1:ℤ) ≤ 1 ∧ (0:ℤ) < 2 ∧ (0:ℤ) < 3 ∧
    (2:ℤ) * 2 + 1 * 3 = 2 * 2 * 3 - 1 * (3 * 3 - 2 * 2) ∧
    (1:ℤ) * (3 * 3 - 2 * 2) ≤ 2 * 2 * 3 - 2 - 3 := by norm_num

/-- Coprimality witness for colred_x_congruence. -/
theorem colred_coprime_witness : IsCoprime (3:ℤ) 2 := by norm_num [IsCoprime]

#print axioms colred_reduction
#print axioms colred_k_one
#print axioms colred_k_bound
#print axioms colred_x_congruence
#print axioms colred_one_per_k
#print axioms colred_k_bound_sharp

end Erdos634.Draft.ColumnReductionWrap
