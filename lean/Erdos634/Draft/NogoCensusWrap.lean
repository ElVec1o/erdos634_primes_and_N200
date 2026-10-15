import Erdos634.CensusSideRelation
import Erdos634.Draft.NogoGamma37Kernel

/-!
# Census statement: abstract wrapper

Packages three sub-results into one named theorem:

1. **γ-junction lower bound**: the minimum γ-junction count over all 10,560 valid
   (word, orientation) configurations is 7 (`minGammaCount37 = 7`), which gives
   `x ≥ 7` at the abstract-configuration level.

2. **Census dependence**: the α- and β-count equations sum to the identity `13 = 13`,
   so they are linearly dependent (carry no information about `x`).

3. **Non-uniqueness**: both `x = 7` and `x = 10` satisfy the equations, so the census
   does not determine `x`.

Here `x` is the junction count of a real tiling's side, while (1) ranges over abstract
configurations; the geometric bridge (junctions carry straight figures, counted by
`gammaJunctionCount`) is not part of this file.  Standard axioms [propext, Classical.choice,
Quot.sound] only.
-/

namespace Erdos634.Draft.NogoCensusWrap

open Erdos634.NogoCount37 Erdos634.CensusSide

/-- **Census statement, abstract form.**
All three clauses hold at the combinatorial level:
(1) the minimum γ-junction count across all 10,560 valid abstract configurations is 7
    (supplying `x ≥ 7` abstractly);
(2) the two count equations are linearly dependent (sum to the identity `13 = 13`);
(3) both `x = 7` and `x = 10` occur, so the census does not pin `x`.
Standard axioms only (no `native_decide`). -/
theorem nogoCensus_abstract :
    -- (1) Abstract γ-lower bound: minimum over all valid configurations = 7
    minGammaCount37 = 7 ∧
    -- (2) Census dependence: α+β equations sum to identity
    (∀ u x A B : ℤ, A + B = 2 * (10 - x) →
      ((7 - u) + (x - 7) + A) + (u + (x - 7) + B) = 13) ∧
    -- (3) Both x=7 and x=10 occur; census does not determine x
    (∃ x₁ x₂ : ℤ, x₁ ≠ x₂ ∧
      (∃ u A B : ℤ, A + B = 2 * (10 - x₁) ∧
        (7 - u) + (x₁ - 7) + A = 3 ∧ u + (x₁ - 7) + B = 10) ∧
      (∃ u A B : ℤ, A + B = 2 * (10 - x₂) ∧
        (7 - u) + (x₂ - 7) + A = 3 ∧ u + (x₂ - 7) + B = 10)) :=
  ⟨NogoGamma37Kernel.nogoGammaJunctions_eq_7_std,
   side_equations_dependent,
   census_does_not_determine_x⟩

#print axioms nogoCensus_abstract

end Erdos634.Draft.NogoCensusWrap
