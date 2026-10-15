import Erdos634.FibonacciFamilies

namespace Erdos634.Draft.FibonacciFamiliesWrap

open Erdos634.FibonacciFamilies Nat

theorem ff_D_factors (e f : ℤ) : 4 * f ^ 2 - e ^ 2 = (2 * f - e) * (2 * f + e) :=
  D_factors e f

theorem ff_M_sq_lt_N_iff (e f : ℤ) :
    (f + e) ^ 2 < 3 * f ^ 2 - e ^ 2 ↔ 0 < f ^ 2 - e * f - e ^ 2 :=
  M_sq_lt_N_iff e f

theorem ff_fib_extremal_iff (e f : ℤ) :
    |(f + e) ^ 2 - (3 * f ^ 2 - e ^ 2)| = 2 ↔ |f ^ 2 - e * f - e ^ 2| = 1 :=
  fib_extremal_iff e f

example : ff_D_factors 1 2 = D_factors 1 2 := rfl

#print axioms ff_M_sq_lt_N_iff
#print axioms ff_fib_extremal_iff

end Erdos634.Draft.FibonacciFamiliesWrap
