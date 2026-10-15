import Erdos634.BaseIdentity

/-!
# Base identity algebraic constraints: wrapper

Re-exports results of `BaseIdentity`:
- `equilateral_base_identity`: area equation forces r₃ ρ² = 2N sin A sin B sin C
- `equilateral_base_identity_word`: same with word expansion
- `general_base_identity`: general target two-sided form
- `base_beta_identity_is_vacuous`: base-β identity holds universally (excludes nothing)

Proved by `ring`.  No `sorry`; standard axioms only.
-/

namespace Erdos634.Draft.BaseIdentityWrap

open Erdos634.BaseIdentity

theorem bi_equilateral_base_identity (sA sB sC s S ρ N r₃ : ℝ) (hs : s ≠ 0)
    (hS : S = s * ρ)
    (harea : N * ((1 / 2) * s ^ 2 * (sA * sB * sC)) = (r₃ / 4) * S ^ 2) :
    r₃ * ρ ^ 2 = 2 * N * (sA * sB * sC) :=
  equilateral_base_identity sA sB sC s S ρ N r₃ hs hS harea

theorem bi_equilateral_base_identity_word (sA sB sC s S N x y z r₃ : ℝ) (hs : s ≠ 0)
    (hS : S = x * (s * sA) + y * (s * sB) + z * (s * sC))
    (harea : N * ((1 / 2) * s ^ 2 * (sA * sB * sC)) = (r₃ / 4) * S ^ 2) :
    r₃ * (x * sA + y * sB + z * sC) ^ 2 = 2 * N * (sA * sB * sC) :=
  equilateral_base_identity_word sA sB sC s S N x y z r₃ hs hS harea

theorem bi_general_base_identity (sA sB sC s S₁ S₂ ρ₁ ρ₂ sθ N : ℝ) (hs : s ≠ 0)
    (h1 : S₁ = s * ρ₁) (h2 : S₂ = s * ρ₂)
    (harea : N * ((1 / 2) * s ^ 2 * (sA * sB * sC)) = (1 / 2) * S₁ * S₂ * sθ) :
    ρ₁ * ρ₂ * sθ = N * (sA * sB * sC) :=
  general_base_identity sA sB sC s S₁ S₂ ρ₁ ρ₂ sθ N hs h1 h2 harea

theorem bi_base_beta_identity_is_vacuous (e f : ℤ) :
    f ^ 3 * (e * (3 * f ^ 2 - e ^ 2)) = (3 * f ^ 2 - e ^ 2) * (e * f) * f ^ 2 :=
  base_beta_identity_is_vacuous e f

-- Non-vacuity
example : (1 : ℤ) ^ 3 * (1 * (3 * 1 ^ 2 - 1 ^ 2)) =
    (3 * 1 ^ 2 - 1 ^ 2) * (1 * 1) * 1 ^ 2 := by norm_num

#print axioms bi_equilateral_base_identity
#print axioms bi_base_beta_identity_is_vacuous

end Erdos634.Draft.BaseIdentityWrap
