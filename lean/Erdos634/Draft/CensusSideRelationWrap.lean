import Erdos634.CensusSideRelation

/-!
# Census-side relation: wrapper

Re-exports results of `CensusSide`:
- `side_equations_dependent`: the two slot equations always sum to 13
- `census_does_not_determine_x`: census alone does not pin x

No `sorry`; standard axioms only.
-/

namespace Erdos634.Draft.CensusSideRelationWrap

open Erdos634.CensusSide

theorem csr_side_equations_dependent (u x A B : ℤ) (hslots : A + B = 2 * (10 - x)) :
    ((7 - u) + (x - 7) + A) + (u + (x - 7) + B) = 13 :=
  side_equations_dependent u x A B hslots

theorem csr_census_does_not_determine_x :
    ∃ x₁ x₂ : ℤ, x₁ ≠ x₂ ∧
      (∃ u A B : ℤ, A + B = 2 * (10 - x₁) ∧ (7 - u) + (x₁ - 7) + A = 3 ∧
        u + (x₁ - 7) + B = 10) ∧
      (∃ u A B : ℤ, A + B = 2 * (10 - x₂) ∧ (7 - u) + (x₂ - 7) + A = 3 ∧
        u + (x₂ - 7) + B = 10) :=
  census_does_not_determine_x

-- Non-vacuity: side_equations_dependent
example : ((7 : ℤ) - 7) + (10 - 7) + 0 + (7 + (10 - 7) + 0) = 13 :=
  csr_side_equations_dependent 7 10 0 0 (by ring)

#print axioms csr_census_does_not_determine_x

end Erdos634.Draft.CensusSideRelationWrap
