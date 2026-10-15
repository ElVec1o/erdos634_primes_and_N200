import Erdos634.Frontier

/-!
# Extra base columns at a close pair: arithmetic kernel

At a close-pair member (coprime e < f with f close to
golden-ratio multiples of e), the surviving extra base columns satisfy three simultaneous
arithmetic constraints: x·e + z·f = 2ef − k·b, f ∣ x − ke, and k·b ≤ 2ef − 3e − f.

The arithmetic content is proved in `Frontier.lean`:

1. **`one_column_per_k`**: for `1 ≤ k`, `qf ≤ ke`, `ke < (q+1)f`, we have `e(1+q) ≤ kf`.
   This bounds how many extra columns a single k can generate.

2. **`close_pair_column`**: the three-variable base equation for a corner-parallelogram-filtered
   column reduces to: `x·e + z·f = 2ef − k·b`, `f ∣ x − ke`, `k·b ≤ 2ef − 3e − f`.

"Surviving extra base column" is a placement statement (the column needs a real base-β tiling to
have meaning); only the arithmetic reduction is formalized here.
-/

namespace Erdos634.Draft.ClosePairColWrap

open Erdos634.Frontier

/-- One column per k: the bound e(1+q) ≤ kf. -/
theorem close_pair_one_per_k {e f k q : ℕ} (he : 0 < e) (hef : e < f) (hk : 1 ≤ k)
    (hq : q * f ≤ k * e) (hq' : k * e < (q + 1) * f) : e * (1 + q) ≤ k * f :=
  one_column_per_k he hef hk hq hq'

/-- Close-pair column reduction: the base equation with x,z≥1, x+z≥4 implies three constraints. -/
theorem close_pair_col_reduction {e f k x z : ℤ}
    (he : 0 < e) (hef : e < f) (hf : f ≠ 0) (hco : IsCoprime f e)
    (hx : 1 ≤ x) (hz : 1 ≤ z) (hxz : 4 ≤ x + z)
    (hbase : x * (e * f) + (e + k * f) * (f * f - e * e) + z * (f * f)
             = e * (3 * f * f - e * e)) :
    x * e + z * f = 2 * e * f - k * (f * f - e * e)
    ∧ f ∣ x - k * e
    ∧ k * (f * f - e * e) ≤ 2 * e * f - 3 * e - f :=
  close_pair_column he hef hf hco hx hz hxz hbase

/-- Non-vacuity for one_column_per_k: at e=2, f=3, k=2, q=1: qf=3≤ke=4 and ke=4<(q+1)f=6. -/
theorem close_pair_col_witness :
    (0 : ℕ) < 2 ∧ (2 : ℕ) < 3 ∧ (1 : ℕ) ≤ 2 ∧
    1 * 3 ≤ 2 * 2 ∧ 2 * 2 < (1 + 1) * 3 ∧ 2 * (1 + 1) ≤ 2 * 3 := by norm_num

#print axioms close_pair_one_per_k
#print axioms close_pair_col_reduction

end Erdos634.Draft.ClosePairColWrap
