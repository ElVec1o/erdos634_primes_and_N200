import Erdos634.OrderForcing

/-!
# Top junction: `p ≤ f−3` for `f ≥ 4`, arithmetic kernel

At `f ≥ 4`, the top junction's parameter satisfies `p ≤ f−3`.
At `f = 3`, the filler is forced direct. The arithmetic has four steps:

1. **`mirrored_filler_outside`**: for `f ≥ 3`, `3f² < f³ + 1`. This rules out the mirrored
   filler: a mirrored tile overruns the top position when f ≥ 3.

2. **`direct_filler_outside`**: for `f ≥ 4`, `3f² + f < f³ + 1`. This rules out the direct
   filler at f ≥ 4; together with the mirrored case, the top has c-count ≥ 3.

3. **`p_le_f_sub_three`**: if `R + p = f` and `R ≥ 3`, then `p ≤ f − 3`. This is the
   final arithmetic step translating c-count ≥ 3 into the parameter bound.

4. **`two_c_single_run`**: with two c-edges pinned at ends, all interior positions are a-edges
   (a single a-run between the two c's).

Not covered: the "top junction" and the block tiles `Cⱼ/Mⱼ` have no Lean definition;
the geometric meaning of p is a placement statement.

0 sorry, no axioms (pure nlinarith/omega).
-/

namespace Erdos634.Draft.TopJunctionWrap

open Erdos634.OrderForcing

/-- The mirrored-filler discriminant is positive: 3f² < f³+1 for f ≥ 3. -/
theorem top_junction_mirrored_out {f : ℕ} (hf : 3 ≤ f) : 3 * f ^ 2 < f ^ 3 + 1 :=
  mirrored_filler_outside hf

/-- The direct-filler discriminant is positive: 3f²+f < f³+1 for f ≥ 4. -/
theorem top_junction_direct_out {f : ℕ} (hf : 4 ≤ f) : 3 * f ^ 2 + f < f ^ 3 + 1 :=
  direct_filler_outside hf

/-- With c-count R ≥ 3 and R + p = f, the parameter satisfies p ≤ f − 3. -/
theorem top_junction_p_bound {f p R : ℕ} (hR : R + p = f) (h3 : 3 ≤ R) : p ≤ f - 3 :=
  p_le_f_sub_three hR h3

/-- Two pinned c-edges force a single a-run in between. -/
theorem top_junction_single_run (n : ℕ) (w : ℕ → Bool)
    (hc : ∀ i, i < n → (w i = false ↔ (i = 0 ∨ i = n - 1)))
    {k : ℕ} (h0 : 0 < k) (hk : k < n - 1) : w k = true :=
  two_c_single_run n w hc h0 hk

/-- Non-vacuity: at f=4, R=3, p=1: R+p=4, R≥3, p≤1. -/
theorem top_junction_witness : (3 : ℕ) + 1 = 4 ∧ (3 : ℕ) ≤ 3 ∧ (1 : ℕ) ≤ 4 - 3 := by norm_num

#print axioms top_junction_mirrored_out
#print axioms top_junction_direct_out
#print axioms top_junction_p_bound

end Erdos634.Draft.TopJunctionWrap
