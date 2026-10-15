import Erdos634.GlobalSystem

/-!
# Corner count system analysis (wrapper for `GlobalSystem`)

Key results:
- `euler_parity`: N odd ↔ B even from Euler relation
- `solution_eleven`: N=11 satisfies all corner count equations
- `prime_solution_exists`: a prime order admits a system solution
- `system_iff_reduced`: system reduces to one equation (v1 pinned)
- `solCount_11/23/47`: kernel-verified solution counts at N=11, 23, 47

0 sorry, standard axioms.
-/

namespace Erdos634.Draft.GlobalSystemWrap

open Erdos634.GlobalSystem

theorem gs_euler_parity (N I B : ℕ) (h : N = 2 * I + B + 1) : Odd N ↔ Even B :=
  euler_parity N I B h

theorem gs_solution_eleven :
    3 + 0 + 3 * 0 + 2 * 4 + 4 * 0 + 6 * 0 = 11 ∧
    2 + 0 + 2 * 0 + 1 + 2 * 4 + 3 * 0 + 4 * 0 = 11 ∧
    0 + 3 * 1 + 2 * 4 + 0 = 11 ∧
    11 = 2 * (1 + 4 + 0 + 0) + (0 + 0) + 1 :=
  solution_eleven

theorem gs_prime_solution_exists :
    ∃ N n₁ n₂ v₁ v₂ v₃ v₄ : ℕ, Nat.Prime N ∧
      3 + n₁ + 3 * n₂ + 2 * v₂ + 4 * v₃ + 6 * v₄ = N ∧
      2 + n₁ + 2 * n₂ + v₁ + 2 * v₂ + 3 * v₃ + 4 * v₄ = N ∧
      n₁ + 3 * v₁ + 2 * v₂ + v₃ = N ∧
      N = 2 * (v₁ + v₂ + v₃ + v₄) + (n₁ + n₂) + 1 :=
  prime_solution_exists

theorem gs_system_iff_reduced (N n1 n2 v1 v2 v3 v4 : ℕ) :
    (3 + n1 + 3 * n2 + 2 * v2 + 4 * v3 + 6 * v4 = N ∧
     2 + n1 + 2 * n2 + v1 + 2 * v2 + 3 * v3 + 4 * v4 = N ∧
     n1 + 3 * v1 + 2 * v2 + v3 = N ∧
     N = 2 * (v1 + v2 + v3 + v4) + (n1 + n2) + 1)
    ↔ (v1 = 1 + n2 + v3 + 2 * v4 ∧ n1 + 3 * n2 + 2 * v2 + 4 * v3 + 6 * v4 + 3 = N) :=
  system_iff_reduced N n1 n2 v1 v2 v3 v4

theorem gs_solCount_11 : solCount 8 = 17 := solCount_11
theorem gs_solCount_23 : solCount 20 = 172 := solCount_23
theorem gs_solCount_47 : solCount 44 = 2096 := solCount_47

-- Non-vacuity: solution_eleven gives ground facts
example : (11 : ℕ) = 2 * (1 + 4 + 0 + 0) + (0 + 0) + 1 := gs_solution_eleven.2.2.2

#print axioms gs_prime_solution_exists
#print axioms gs_system_iff_reduced
#print axioms gs_solCount_47

end Erdos634.Draft.GlobalSystemWrap
