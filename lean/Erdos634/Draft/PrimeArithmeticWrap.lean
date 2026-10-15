import Erdos634.PrimeArithmetic

/-!
# PrimeArithmetic — prime exclusion arithmetic: wrapper

Key results:
- `not_prime_of_two_le`: product of two factors ≥ 2 is not prime
- `prime_count_forces_scale`: prime count forces b=k², N=a+2b
- `prime_three_mod_four_excluded`: p≡3 mod 4 prime excludes squares, sum of two squares, etc.
- `prime_sum_two_pos_squares`: p≡1 mod 4 prime is sum of two positive squares
- `F1_count_not_prime`, `F2_count_not_prime`, `F3_count_not_prime`, `F4_count_not_prime`

Standard axioms, no `sorry`.
-/

namespace Erdos634.Draft.PrimeArithmeticWrap

open Erdos634.PrimeArithmetic

theorem pa_not_prime_of_two_le (u v : ℤ) (hu : 2 ≤ u) (hv : 2 ≤ v) : ¬ Prime (u * v) :=
  not_prime_of_two_le u v hu hv

theorem pa_prime_count_forces_scale (a b k N : ℤ) (ha : 0 < a) (hb : 0 < b) (hk : 0 < k)
    (hcop : IsCoprime a b) (hN : Prime N) (harea : N * b = k ^ 2 * (a + 2 * b)) :
    b = k ^ 2 ∧ N = a + 2 * b :=
  prime_count_forces_scale a b k N ha hb hk hcop hN harea

theorem pa_prime_three_mod_four_excluded (p : ℕ) (hp : p.Prime) (h4 : p % 4 = 3)
    (h3 : 3 < p) :
    (¬ IsSquare p) ∧ (¬ ∃ x y : ℕ, x ^ 2 + y ^ 2 = p) ∧
    (¬ ∃ k, p = 2 * k ^ 2) ∧ (¬ ∃ k, p = 3 * k ^ 2) ∧ (¬ ∃ k, p = 6 * k ^ 2) :=
  prime_three_mod_four_excluded p hp h4 h3

theorem pa_prime_sum_two_pos_squares (p : ℕ) (hp : p.Prime) (h4 : p % 4 ≠ 3) :
    ∃ e f : ℕ, 1 ≤ e ∧ 1 ≤ f ∧ e ^ 2 + f ^ 2 = p :=
  prime_sum_two_pos_squares p hp h4

theorem pa_F1_count_not_prime (a b c t : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hcop : IsCoprime a b) (hc2 : c ^ 2 = a ^ 2 + a * b + b ^ 2) (ht : 1 ≤ t) :
    ¬ Prime (t * (a + b)) :=
  F1_count_not_prime a b c t ha hb hc hcop hc2 ht

theorem pa_F2_count_not_prime (a b : ℤ) (ha : 0 < a) (hb : 0 < b) :
    ¬ Prime ((a + 2 * b) * (2 * a + b)) :=
  F2_count_not_prime a b ha hb

theorem pa_F3_count_not_prime (a b : ℤ) (ha : 0 < a) (hb : 0 < b) :
    ¬ Prime (3 * ((a + b) * (a + 2 * b))) :=
  F3_count_not_prime a b ha hb

theorem pa_F4_count_not_prime (a b : ℤ) (ha : 0 < a) (hb : 0 < b) :
    ¬ Prime ((a + b) * (2 * a + b)) :=
  F4_count_not_prime a b ha hb

-- Non-vacuity: p=7 is prime with 7%4=3
example : ¬ IsSquare (7 : ℕ) :=
  (pa_prime_three_mod_four_excluded 7 (by norm_num) (by norm_num) (by norm_num)).1

#print axioms pa_prime_sum_two_pos_squares
#print axioms pa_prime_three_mod_four_excluded

end Erdos634.Draft.PrimeArithmeticWrap
