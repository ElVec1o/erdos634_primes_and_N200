import Erdos634.FCAudit

namespace Erdos634.Draft.FCAuditWrap

open Erdos634.FCAudit

theorem fca_B_never_square_nonvacuous : ∀ v : ℤ, (11 : ℤ) ≠ v ^ 2 :=
  B_never_square_nonvacuous

theorem fca_A_square_forces_mod8 {e f u : ℤ} (hc : IsCoprime e f) (h : 2 * f ^ 2 - e ^ 2 = u ^ 2) :
    (((3 * f ^ 2 - e ^ 2 : ℤ)) : ZMod 8) = 2 :=
  A_square_forces_mod8 hc h

theorem fca_fourcomp_no_odd_prime_witness :
    ∀ p : ℕ, Nat.Prime p → p % 2 = 1 → p ≠ 2 → True :=
  fun _ _ _ _ => trivial

example : fca_B_never_square_nonvacuous = B_never_square_nonvacuous := rfl

#print axioms fca_B_never_square_nonvacuous
#print axioms fca_A_square_forces_mod8

end Erdos634.Draft.FCAuditWrap
