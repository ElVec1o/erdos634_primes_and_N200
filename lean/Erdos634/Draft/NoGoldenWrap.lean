import Erdos634.ApexRigidity

/-!
# The golden-ratio hypothesis: arithmetic kernel

The hypothesis φ = b/a (golden ratio) can be dropped from the base-β analysis.  The key arithmetic:
`b > f` at every member, and `e·b > a`, which kills every
representation of `a − b` as a non-negative combination of `{a, b, c}`.  Therefore the branch
where a `b`-edge could straddle the `a`-side does not arise; the case `b < a` forces `e ≥ 2`, so `e = 1`
is not affected by the golden-ratio condition.

The arithmetic content is in `ApexRigidity.lean`:

1. **`b_gt_f`**: at every base-β member with `e < f`, `f + e² < f²`. Equivalently `b > f`
   (since `b = f² − e²` in unsigned arithmetic; this form avoids truncated subtraction).

2. **`eb_gt_a`**: `e·f < e·(f²−e²)`, i.e. `e·b > a` (the kill inequality).

3. **`e_ge_two_of_b_lt_a`**: if `f²−e² < e·f` then `e ≥ 2`. So at `e = 1`, `b ≥ a`, and
   the `b < a` branch is empty.

This file contains only these side-length inequalities; it makes no statement about
`CongruentDissection`s.  Standard axioms, no `sorry`.
-/

namespace Erdos634.Draft.NoGoldenWrap

open Erdos634.ApexRigidity

/-- At every base-β member, b > f (stated: f + e² < f²). -/
theorem nogolden_b_gt_f {e f : ℕ} (hef : e < f) (hf : 2 ≤ f) : f + e ^ 2 < f ^ 2 :=
  b_gt_f hef hf

/-- At every base-β member, e·b > a (stated: e·f < e·(f²−e²)). -/
theorem nogolden_eb_gt_a {e f : ℕ} (he : 1 ≤ e) (hef : e < f) (hf : 2 ≤ f) :
    e * f < e * (f ^ 2 - e ^ 2) :=
  eb_gt_a he hef hf

/-- If b < a at a base-β member, then e ≥ 2 (so e = 1 cannot have b < a). -/
theorem nogolden_e_ge_two {e f : ℕ} (he : 1 ≤ e) (hf : 2 ≤ f) (hef : e < f)
    (hba : f ^ 2 - e ^ 2 < e * f) : 2 ≤ e :=
  e_ge_two_of_b_lt_a he hf hef hba

/-- Non-vacuity: at (e,f) = (2,3), b = 5, a = 6, f = 3: b_gt_f and eb_gt_a hold. -/
theorem nogolden_witness : (2 : ℕ) < 3 ∧ (2 : ℕ) ≤ 3 ∧
    3 + 2 ^ 2 < 3 ^ 2 ∧ 2 * 3 < 2 * (3 ^ 2 - 2 ^ 2) := by norm_num

#print axioms nogolden_b_gt_f
#print axioms nogolden_eb_gt_a
#print axioms nogolden_e_ge_two

end Erdos634.Draft.NoGoldenWrap
