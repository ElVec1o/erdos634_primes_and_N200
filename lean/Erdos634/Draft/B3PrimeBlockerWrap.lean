import Erdos634.B3PrimeBlocker

/-!
# Two facts about the equation `N = 2K² − M²` in the prime case: wrapper

Re-exports, under `b3pb_` names, results of `B3PrimeBlocker`:
- `hypothesis_not_automatic`: K ∤ M² and K ∤ N for the (2,3,4) tiling certificate
- `equation_alone_excludes_nothing`: N = 2K²−M² is prime without K ∣ N
- `conditional_still_holds`: the original conditional statement still holds

No `sorry`; standard axioms only.
-/

namespace Erdos634.Draft.B3PrimeBlockerWrap

open Erdos634.B3PrimeBlocker

theorem b3pb_hypothesis_not_automatic :
    ¬ ((6:ℕ) ∣ 3 ^ 2) ∧ ¬ ((6:ℕ) ∣ 63) ∧ 63 = 2 * 6 ^ 2 - 3 ^ 2 :=
  hypothesis_not_automatic

theorem b3pb_equation_alone_excludes_nothing :
    (2 * 2 ^ 2 - 1 ^ 2 = 7 ∧ Nat.Prime 7) ∧
    (2 * 3 ^ 2 - 1 ^ 2 = 17 ∧ Nat.Prime 17) ∧
    (2 * 4 ^ 2 - 3 ^ 2 = 23 ∧ Nat.Prime 23) ∧
    (2 * 6 ^ 2 - 5 ^ 2 = 47 ∧ Nat.Prime 47) :=
  equation_alone_excludes_nothing

theorem b3pb_conditional_still_holds (N K M : ℕ) (hN : N.Prime) (hodd : Odd N)
    (hK : K ∣ N) (heq : N + M ^ 2 = 2 * K ^ 2) : False :=
  conditional_still_holds N K M hN hodd hK heq

-- Non-vacuity: hypothesis is false (6 ∤ 9)
example : ¬ ((6:ℕ) ∣ 9) := b3pb_hypothesis_not_automatic.1

#print axioms b3pb_hypothesis_not_automatic
#print axioms b3pb_conditional_still_holds

end Erdos634.Draft.B3PrimeBlockerWrap
