import Erdos634.NormForm

namespace Erdos634.Draft.NormFormWrap
open Erdos634.NormForm

theorem wrap_prime_values :
    Nat.Prime (3 * 2 ^ 2 - 1 ^ 2) ∧ Nat.Prime (3 * 3 ^ 2 - 2 ^ 2) ∧
    Nat.Prime (3 * 4 ^ 2 - 1 ^ 2) ∧ Nat.Prime (3 * 5 ^ 2 - 2 ^ 2) :=
  prime_values

example : True := trivial
#print axioms wrap_prime_values

end Erdos634.Draft.NormFormWrap
