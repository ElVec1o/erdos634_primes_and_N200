import Erdos634.FourCompCongruence

/-!
# Wrapper: `FourCompCongruence` — congruence obstructions for the `(2α,α,2β)` branch

Thin delegation layer exposing the four key theorems of
`Erdos634.FourCompCongruence` under the `Draft` namespace.
No `sorry`; standard axioms only.
-/

namespace Erdos634.Draft.FourCompCongruenceWrap

open Erdos634.FourCompCongruence

/-- Coprime integers are not both even. -/
theorem not_both_even_X {e f : ℤ} (hc : IsCoprime e f) :
    ¬ ((2 : ℤ) ∣ e ∧ (2 : ℤ) ∣ f) :=
  not_both_even hc

/-- `B = 3f² − e²` is never a perfect square when `gcd(e,f) = 1` (mod 3 argument). -/
theorem B_never_square_X {e f v : ℤ} (hc : IsCoprime e f) :
    3 * f ^ 2 - e ^ 2 ≠ v ^ 2 :=
  B_never_square hc

/-- If `A = 2f² − e²` is a perfect square and `gcd(e,f) = 1`, then `B ≡ 2 (mod 4)`. -/
theorem A_square_forces_X {e f u : ℤ} (hc : IsCoprime e f)
    (h : 2 * f ^ 2 - e ^ 2 = u ^ 2) :
    (((3 * f ^ 2 - e ^ 2 : ℤ)) : ZMod 4) = 2 :=
  A_square_forces hc h

/-- In the surviving branch, `N` prime forces `N = 2` (mod 4 argument). -/
theorem fourcomp_prime_eq_two_X {e f u v : ℤ} {N : ℕ}
    (hc : IsCoprime e f) (hN : Nat.Prime N)
    (hA : 2 * f ^ 2 - e ^ 2 = u ^ 2)
    (hB : 3 * f ^ 2 - e ^ 2 = (N : ℤ) * v ^ 2) :
    N = 2 :=
  fourcomp_prime_eq_two hc hN hA hB

/-- No odd prime `N` survives the coprime split: whichever branch holds, `N = 2`. -/
theorem fourcomp_no_odd_prime_X {e f : ℤ} {N : ℕ}
    (hc : IsCoprime e f) (hN : Nat.Prime N)
    (hsplit :
      (∃ u v : ℤ, 2 * f ^ 2 - e ^ 2 = (N : ℤ) * u ^ 2 ∧ 3 * f ^ 2 - e ^ 2 = v ^ 2) ∨
      (∃ u v : ℤ, 2 * f ^ 2 - e ^ 2 = u ^ 2 ∧ 3 * f ^ 2 - e ^ 2 = (N : ℤ) * v ^ 2)) :
    N = 2 :=
  fourcomp_no_odd_prime hc hN hsplit

/-! ### Non-vacuity witness

`e = 1, f = 2` satisfies `IsCoprime e f`, so `not_both_even_X` is non-trivially applicable. -/

/-- Non-vacuity: `IsCoprime 1 2` and the pair is not both even. -/
example : ¬ ((2 : ℤ) ∣ 1 ∧ (2 : ℤ) ∣ 2) :=
  not_both_even_X isCoprime_one_left

#print axioms fourcomp_no_odd_prime_X

end Erdos634.Draft.FourCompCongruenceWrap
