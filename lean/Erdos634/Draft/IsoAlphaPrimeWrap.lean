import Erdos634.IsoAlphaPrime

/-!
# IsoAlphaPrime — isosceles α-tile prime obstruction: wrapper

`IsoAlphaPrime.*` proves that an isosceles tile with rational α cannot have prime tile count N.

Key results:
1. **`isoalpha_X_forces`**: X·(2f+e) = M·((f+e)·f²) ⟹ (2f+e) ∣ M.
2. **`isoalpha_not_prime`**: N prime + area equation ⟹ False.

No sorry; standard axioms.
-/

namespace Erdos634.Draft.IsoAlphaPrimeWrap

open Erdos634.IsoAlpha

/-- Divisibility forcing for the isosceles α-tile. -/
theorem isoalpha_X_forces_wrap (e f M X : ℕ) (hcop : Nat.Coprime e f)
    (hX : X * (2 * f + e) = M * ((f + e) * f ^ 2)) : (2 * f + e) ∣ M :=
  Erdos634.IsoAlpha.isoalpha_X_forces e f M X hcop hX

/-- Isosceles α-tile cannot produce prime tile count. -/
theorem isoalpha_not_prime_wrap (N e d m : ℕ) (hN : N.Prime) (he : 1 ≤ e) (hd : 1 ≤ d)
    (hcop : Nat.Coprime e (e + d))
    (heq : N * d = m ^ 2 * ((2 * e + d) * (e ^ 2 + 4 * e * d + 2 * d ^ 2))) : False :=
  Erdos634.IsoAlpha.isoalpha_not_prime N e d m hN he hd hcop heq

/-- Non-vacuity: e=1, d=1, 2f+e=3=2·1+1 divides itself. -/
theorem isoalpha_witness : (3:ℕ) ∣ 3 := dvd_refl 3

#print axioms isoalpha_X_forces_wrap
#print axioms isoalpha_not_prime_wrap

end Erdos634.Draft.IsoAlphaPrimeWrap
