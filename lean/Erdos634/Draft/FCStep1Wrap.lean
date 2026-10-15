import Erdos634.FCStep1

/-!
# Wrapper: `FCStep1` — coprime factorization, steps (1)–(3)

Thin delegation layer exposing the key theorems of `Erdos634.FCStep1` under the `Draft` namespace.
No `sorry`; standard axioms only.
-/

namespace Erdos634.Draft.FCStep1Wrap

open Erdos634.FCStep1

/-- **Step (1).** For coprime `e, f`, `gcd(A, B) = 1` where `A = 2f²−e²`, `B = 3f²−e²`. -/
theorem gcd_A_B_X {e f : ℤ} (hc : IsCoprime e f) :
    IsCoprime (2 * f ^ 2 - e ^ 2) (3 * f ^ 2 - e ^ 2) :=
  gcd_A_B hc

/-- The same statement with `Int.gcd` phrasing. -/
theorem gcd_A_B_int_gcd_X {e f : ℤ} (hc : Int.gcd e f = 1) :
    Int.gcd (2 * f ^ 2 - e ^ 2) (3 * f ^ 2 - e ^ 2) = 1 :=
  gcd_A_B_int_gcd hc

/-- The same statement for natural-number parameters. -/
theorem gcd_A_B_nat_X {e f : ℕ} (hc : Nat.Coprime e f) :
    Int.gcd (2 * (f : ℤ) ^ 2 - (e : ℤ) ^ 2) (3 * (f : ℤ) ^ 2 - (e : ℤ) ^ 2) = 1 :=
  gcd_A_B_nat hc

/-- `A · B` is never a perfect square on the coprime range `0 < e < f`. -/
theorem AB_never_square_X {e f c : ℤ} (hc : IsCoprime e f)
    (he : 0 < e) (hef : e < f) :
    (2 * f ^ 2 - e ^ 2) * (3 * f ^ 2 - e ^ 2) ≠ c ^ 2 :=
  AB_never_square hc he hef

/-- **Steps (2)–(3).** From `A · B = N · w²` with `N` prime and `0 < e < f` coprime,
the prime lands wholly in one factor. -/
theorem split_of_prime_X {e f w : ℤ} {N : ℕ}
    (hc : IsCoprime e f) (he : 0 < e) (hef : e < f) (hN : Nat.Prime N)
    (heq : (2 * f ^ 2 - e ^ 2) * (3 * f ^ 2 - e ^ 2) = (N : ℤ) * w ^ 2) :
    (∃ u v : ℤ, 2 * f ^ 2 - e ^ 2 = (N : ℤ) * u ^ 2 ∧ 3 * f ^ 2 - e ^ 2 = v ^ 2) ∨
    (∃ u v : ℤ, 2 * f ^ 2 - e ^ 2 = u ^ 2 ∧ 3 * f ^ 2 - e ^ 2 = (N : ℤ) * v ^ 2) :=
  split_of_prime hc he hef hN heq

/-- **The chain.** `A · B = N · w²` with `N` prime and `0 < e < f` coprime forces `N = 2`.
Beeson III Theorem 11 is used nowhere. -/
theorem fourcomp_AB_prime_eq_two_X {e f w : ℤ} {N : ℕ}
    (hc : IsCoprime e f) (he : 0 < e) (hef : e < f) (hN : Nat.Prime N)
    (heq : (2 * f ^ 2 - e ^ 2) * (3 * f ^ 2 - e ^ 2) = (N : ℤ) * w ^ 2) :
    N = 2 :=
  fourcomp_AB_prime_eq_two hc he hef hN heq

/-! ### Non-vacuity witness

`e = 1, f = 2`: `A = 7`, `B = 11`, both prime, and `IsCoprime 7 11`. -/

/-- Non-vacuity: `gcd_A_B_X` at `e = 1, f = 2` asserts `IsCoprime 7 11`. -/
example : IsCoprime (7 : ℤ) 11 := by
  have h := gcd_A_B_X (e := 1) (f := 2) isCoprime_one_left
  have e1 : 2 * (2 : ℤ) ^ 2 - 1 ^ 2 = 7 := by norm_num
  have e2 : 3 * (2 : ℤ) ^ 2 - 1 ^ 2 = 11 := by norm_num
  rwa [e1, e2] at h

#print axioms fourcomp_AB_prime_eq_two_X

end Erdos634.Draft.FCStep1Wrap
