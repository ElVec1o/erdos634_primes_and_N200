-- Draft/DiscNotSquarePrime.lean — disc_not_square extended to prime N > 3 (covers N=5).
-- `InvariantProduct.disc_not_square` requires `6 < N`, which misses N=5.
-- This file adds `disc_not_square_prime`: for any prime N > 3, N² + 14N + 1 is not a square.
-- Proof: N=5 checked directly (D=96, between 9²=81 and 10²=100); N>6 uses disc_not_square.
-- No sorry.  On the closure of `theoremP_6` via F1IrrationalRatio (not a direct `All` import).

import Erdos634.InvariantProduct

open scoped Classical

namespace Erdos634.Draft.DiscPrime

open Erdos634.InvariantProduct

/-- For any prime `N > 3`, the discriminant `N² + 14N + 1` is not a perfect square.
(Extension of `disc_not_square` to cover N = 5, which satisfies `3 < 5 ≤ 6`.) -/
theorem disc_not_square_prime (N : ℕ) (q : ℤ) (hprime : N.Prime) (h3 : 3 < N) :
    (N : ℤ) ^ 2 + 14 * (N : ℤ) + 1 ≠ q ^ 2 := by
  -- Either N ≤ 6 (hence N = 5 by primality + h3) or N > 6 (use disc_not_square)
  rcases Nat.lt_or_ge N 7 with h6 | h6
  · -- 3 < N < 7 and N prime ⟹ N = 5
    have hN5 : N = 5 := by
      interval_cases N
      · exact absurd hprime (by norm_num)
      · rfl
      · exact absurd hprime (by norm_num)
    subst hN5
    -- D = 25 + 70 + 1 = 96; 9² = 81 < 96 < 100 = 10²: no integer square
    intro h
    have hq96 : q ^ 2 = 96 := by push_cast at h; linarith
    have h1 : q ≤ 9 := by nlinarith [sq_nonneg (q - 10)]
    have h2 : -9 ≤ q := by nlinarith [sq_nonneg (q + 10)]
    interval_cases q <;> omega
  · -- N ≥ 7 > 6: apply disc_not_square
    exact disc_not_square (N : ℤ) q (by exact_mod_cast h6)

#print axioms disc_not_square_prime

/-- For any prime `N ≥ 2`, the discriminant `N² + 14N + 1` is not a perfect square.
Extends `disc_not_square_prime` to cover N = 2 and N = 3. -/
theorem disc_not_square_prime_ge2 (N : ℕ) (q : ℤ) (hprime : N.Prime) :
    (N : ℤ) ^ 2 + 14 * (N : ℤ) + 1 ≠ q ^ 2 := by
  rcases Nat.lt_or_ge N 4 with h3 | h3
  · -- N < 4 and N prime: N = 2 or N = 3 (N=0,1 not prime)
    have hN2 : 2 ≤ N := hprime.two_le
    interval_cases N
    · -- N = 2: D = 4+28+1 = 33; 5²=25 < 33 < 36=6²
      intro h
      have : q ^ 2 = 33 := by push_cast at h; linarith
      have h1 : q ≤ 5 := by nlinarith [sq_nonneg (q - 6)]
      have h2 : -5 ≤ q := by nlinarith [sq_nonneg (q + 6)]
      interval_cases q <;> omega
    · -- N = 3: D = 9+42+1 = 52; 7²=49 < 52 < 64=8²
      intro h
      have : q ^ 2 = 52 := by push_cast at h; linarith
      have h1 : q ≤ 7 := by nlinarith [sq_nonneg (q - 8)]
      have h2 : -7 ≤ q := by nlinarith [sq_nonneg (q + 8)]
      interval_cases q <;> omega
  · -- N ≥ 4 (prime ≥ 4 means N > 3): apply disc_not_square_prime
    exact disc_not_square_prime N q hprime (by omega)

#print axioms disc_not_square_prime_ge2

end Erdos634.Draft.DiscPrime
