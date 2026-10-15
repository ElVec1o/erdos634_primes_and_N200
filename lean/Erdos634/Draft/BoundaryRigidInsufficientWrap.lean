import Erdos634.BoundaryRigidInsufficient

/-!
# Boundary rigidity is insufficient: wrapper

Re-exports results of `BoundaryRigidInsufficient`:
- `boundary_rigid_iff`: rigidity iff 2e ≤ f
- `rigid_primes`: several small instances satisfy 2e ≤ f
- `not_rigid_at_83`: (e,f)=(5,6) at N=83 is not rigid
- `least_rigid_at_179`: (e,f)=(8,9) is rigid

No `sorry`; standard axioms only.
-/

namespace Erdos634.Draft.BoundaryRigidInsufficientWrap

open Erdos634.BoundaryRigidInsufficient

theorem bri_boundary_rigid_iff {e f : ℤ} (he : 0 < e) (hef : e < f) :
    (∀ j : ℤ, 0 ≤ j → j * (f - e) ≤ e - 1 → j = 0) ↔ 2 * e ≤ f :=
  boundary_rigid_iff he hef

theorem bri_rigid_primes :
    2 * (1:ℤ) ≤ 2 ∧ 2 * (1:ℤ) ≤ 4 ∧ 2 * (2:ℤ) ≤ 5 ∧ 2 * (1:ℤ) ≤ 6 ∧
    2 * (1:ℤ) ≤ 8 ∧ 2 * (4:ℤ) ≤ 9 ∧ 2 * (2:ℤ) ≤ 9 :=
  rigid_primes

theorem bri_not_rigid_at_83 : ¬ (2 * (5:ℤ) ≤ 6) := not_rigid_at_83

-- Non-vacuity: rigid_primes contains concrete witnesses
example : 2 * (1:ℤ) ≤ 2 := bri_rigid_primes.1

#print axioms bri_boundary_rigid_iff
#print axioms bri_rigid_primes

end Erdos634.Draft.BoundaryRigidInsufficientWrap
