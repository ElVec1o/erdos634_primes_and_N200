import Erdos634.FibExtremal

namespace Erdos634.Draft.FibExtremalWrap

open Erdos634.FibExtremal

theorem fe_two_le_gap (e f : ℤ) (he : 1 ≤ e) (hef : e < f) (hcop : IsCoprime e f) :
    2 ≤ |(f + e) ^ 2 - (3 * f ^ 2 - e ^ 2)| :=
  two_le_gap e f he hef hcop

theorem fe_gap_eq_two_iff (e f : ℤ) :
    |(f + e) ^ 2 - (3 * f ^ 2 - e ^ 2)| = 2 ↔ |f ^ 2 - e * f - e ^ 2| = 1 :=
  gap_eq_two_iff e f

theorem fe_fib_gap (n : ℕ) :
    |((Nat.fib (n + 1) : ℤ) + (Nat.fib n : ℤ)) ^ 2
      - (3 * (Nat.fib (n + 1) : ℤ) ^ 2 - (Nat.fib n : ℤ) ^ 2)| = 2 :=
  fib_gap n

example : fe_gap_eq_two_iff 1 1 = gap_eq_two_iff 1 1 := rfl

#print axioms fe_two_le_gap
#print axioms fe_fib_gap

end Erdos634.Draft.FibExtremalWrap
