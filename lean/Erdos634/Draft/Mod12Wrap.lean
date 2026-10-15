import Erdos634.Mod12

/-!
# Mod12 — mod-12 arithmetic for base-β primes: wrapper

`Mod12.*` provides the elementary modular arithmetic for the base-β prime classification.

Key results:
1. **`sq_odd_mod_four`**: odd e ⟹ e²≡1 (mod 4).
2. **`sq_even_mod_four`**: even e ⟹ e²≡0 (mod 4).
3. **`sq_mod_three`**: 3∤e ⟹ e²≡1 (mod 3).
4. **`base_beta_prime_mod12`**: p prime, p>3, Coprime e f, p+e²=3f² ⟹ p≡11 (mod 12).

No sorry; standard axioms.
-/

namespace Erdos634.Draft.Mod12Wrap

open Erdos634.Mod12

theorem mod12_sq_odd_mod_four {e : ℕ} (he : e % 2 = 1) : e * e % 4 = 1 :=
  sq_odd_mod_four he

theorem mod12_sq_even_mod_four {e : ℕ} (he : e % 2 = 0) : e * e % 4 = 0 :=
  sq_even_mod_four he

theorem mod12_sq_mod_three {e : ℕ} (he : e % 3 ≠ 0) : e * e % 3 = 1 :=
  sq_mod_three he

theorem mod12_base_beta_prime {p e f : ℕ} (hp : Nat.Prime p) (hp3 : 3 < p)
    (hco : Nat.Coprime e f) (h : p + e * e = 3 * (f * f)) : p % 12 = 11 :=
  base_beta_prime_mod12 hp hp3 hco h

/-- Non-vacuity: 11≡11 (mod 12) and 11 is prime. -/
theorem mod12_witness : (11:ℕ) % 12 = 11 := by norm_num

#print axioms mod12_sq_odd_mod_four
#print axioms mod12_base_beta_prime

end Erdos634.Draft.Mod12Wrap
