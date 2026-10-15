import Erdos634.BaseBetaMod12

/-!
# Mod 12 arithmetic kernels: wrapper

Re-exports results of `BaseBetaMod12`:
1. **`basebeta_prime_mod_twelve`**: prime p>3 with p+e²=3f² ⟹ p≡11 (mod 12).
2. **`not_basebeta_of_mod_twelve_ne`**: contrapositive, p≢11 (mod 12) ⟹ no such (e,f).

Pure ℕ arithmetic.  No `sorry`; standard axioms only.
-/

namespace Erdos634.Draft.BaseBetaMod12Wrap

open Erdos634.BaseBetaMod12

/-- Base-β prime ≡ 11 (mod 12): p+e²=3f² with p prime, p>3 ⟹ p%12=11. -/
theorem mod12_prime (p e f : ℕ) (hp : p.Prime) (hp3 : 3 < p)
    (hcop : Nat.Coprime e f) (heq : p + e ^ 2 = 3 * f ^ 2) :
    p % 12 = 11 :=
  basebeta_prime_mod_twelve p e f hp hp3 hcop heq

/-- Non-base-β primes: p%12≠11 ⟹ no coprime (e,f) with p+e²=3f². -/
theorem mod12_not_basebeta (p : ℕ) (hp : p.Prime) (hp3 : 3 < p) (hne : p % 12 ≠ 11) :
    ¬ ∃ e f : ℕ, Nat.Coprime e f ∧ p + e ^ 2 = 3 * f ^ 2 :=
  not_basebeta_of_mod_twelve_ne p hp hp3 hne

/-- Non-vacuity: 11 is prime, 11>3, Coprime 1 2, 11+1=12=3·4. -/
theorem mod12_witness : (11:ℕ).Prime ∧ 3 < 11 ∧ Nat.Coprime 1 2 ∧ 11 + 1^2 = 3 * 2^2 := by
  norm_num [Nat.Coprime]

#print axioms mod12_prime
#print axioms mod12_not_basebeta

end Erdos634.Draft.BaseBetaMod12Wrap
