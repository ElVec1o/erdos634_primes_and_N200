import Erdos634.OrderForcing

/-!
# jb-line partition arithmetic kernel

The only edge decomposition of `j·b` (for `1 ≤ j < f`, `e = 1`, `b = f²−1`) is exactly `j` copies of `b`.
The arithmetic: `x·f + y·(f²−1) + z·f² = j·(f²−1)` with `1 ≤ j < f` implies `(x,y,z) = (0,j,0)`.

The arithmetic content is in `OrderForcing.lean`:

1. **`partition_jb`**: for `3 ≤ f`, `1 ≤ j < f`, `x·f + y·(f·f−1) + z·(f·f) = j·(f·f−1)` implies
   `x = 0`, `y = j`, `z = 0`. Proved by bounding `y ≤ j` from the length constraint, then using
   mod-f divisibility to force `j − y` divisible by `f`, hence zero, so `y = j`; the residual
   vanishes.

The statement that an edged line of length `j·b` carries exactly these tiles is a placement statement and is not
part of this file.

No sorry; axioms [propext, Classical.choice, Quot.sound].
-/

namespace Erdos634.Draft.JbLineWrap

open Erdos634.OrderForcing

/-- jb-line arithmetic: x·f + y·(f²−1) + z·f² = j·(f²−1) ⟹ (x,y,z) = (0,j,0). -/
theorem jbline_partition {f j x y z : ℕ} (hf : 3 ≤ f) (hj1 : 1 ≤ j) (hjf : j < f)
    (h : x * f + y * (f * f - 1) + z * (f * f) = j * (f * f - 1)) :
    x = 0 ∧ y = j ∧ z = 0 :=
  partition_jb hf hj1 hjf h

/-- Non-vacuity: at f=3, j=1: 0·3 + 1·8 + 0·9 = 1·8. -/
theorem jbline_witness :
    (1 : ℕ) ≤ 1 ∧ (1 : ℕ) < 3 ∧ (0 : ℕ) * 3 + 1 * (3 * 3 - 1) + 0 * (3 * 3) = 1 * (3 * 3 - 1) :=
  by norm_num

#print axioms jbline_partition

end Erdos634.Draft.JbLineWrap
