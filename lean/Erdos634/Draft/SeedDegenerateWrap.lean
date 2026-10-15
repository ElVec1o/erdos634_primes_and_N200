import Erdos634.SeedDegenerate

/-!
# The seed interface relations vanish exactly at f=2e: arithmetic kernel

Evaluated at the base-β tile (a,b,c)=(ef,f²−e²,f²), each
of the five interface relations factors as (f−2e) times a positive cofactor. Hence each
relation holds iff f = 2e — the certified (1,2) seeds close on (1,2) and no other member.

Key arithmetic facts in `SeedDegenerate.lean` (ring identities):

1. **`factor_c_two_a`**: c − 2a = f·(f−2e)
2. **`factor_two_b_three_a`**: 2b − 3a = (2f+e)·(f−2e)
3. **`factor_two_b_a_c`**: 2b − (a+c) = (f+e)·(f−2e)
4. **`factor_three_c_four_b`**: 3c − 4b = (f+2e)·(f−2e) + e^2
5. **`factor_a_two_b_two_c`**: a + 2b − 2c = e·(f−2e)

And the biconditionals: each relation holds iff f = 2e.

That these five are the only relations across the eight certified (1,2) tilings is a computation over concrete
tilings and is not part of this module.

0 sorry, standard axioms.
-/

namespace Erdos634.Draft.SeedDegenerateWrap

open Erdos634.SeedDegenerate

/-- Relation 1: c − 2a = f·(f−2e) at the base-β tile. -/
theorem seeddeg_rel1 (e f : ℤ) : cSide f - 2 * aSide e f = f * (f - 2 * e) :=
  factor_c_two_a e f

/-- Relation 2: 2b − 3a = (2f+e)·(f−2e). -/
theorem seeddeg_rel2 (e f : ℤ) : 2 * bSide e f - 3 * aSide e f = (2 * f + e) * (f - 2 * e) :=
  factor_two_b_three_a e f

/-- Relation 3: 2b − (a+c) = (f+e)·(f−2e). -/
theorem seeddeg_rel3 (e f : ℤ) : 2 * bSide e f - (aSide e f + cSide f) = (f + e) * (f - 2 * e) :=
  factor_two_b_a_c e f

/-- The cofactors are positive on 0 < e < f. -/
theorem seeddeg_cofactors_pos {e f : ℤ} (he : 0 < e) (hef : e < f) :
    0 < f ∧ 0 < 2 * f + e ∧ 0 < f + e ∧ 0 < f + 2 * e ∧ 0 < e :=
  cofactors_pos he hef

/-- Each relation holds iff f = 2e (seed-degeneracy condition, requires 0<e<f).
    Representative: c = 2a ↔ f = 2e. -/
theorem seeddeg_iff {e f : ℤ} (he : 0 < e) (hef : e < f) :
    cSide f = 2 * aSide e f ↔ f = 2 * e :=
  c_two_a_iff he hef

/-- All five relations hold at (e,f) = (1,2) — witness that the (1,2) seed is degenerate. -/
theorem seeddeg_at_one_two : cSide 2 = 2 * aSide 1 2 ∧
    2 * bSide 1 2 = 3 * aSide 1 2 ∧
    2 * bSide 1 2 = aSide 1 2 + cSide 2 ∧
    3 * cSide 2 = 4 * bSide 1 2 ∧
    aSide 1 2 + 2 * bSide 1 2 = 2 * cSide 2 :=
  relations_at_one_two

/-- None of the five relations hold at (e,f) = (1,3) — non-degenerate member.
    (The negation is of the disjunction, matching relations_fail_at_one_three.) -/
theorem seeddeg_fail_one_three :
    ¬ (cSide 3 = 2 * aSide 1 3 ∨ 2 * bSide 1 3 = 3 * aSide 1 3 ∨
      2 * bSide 1 3 = aSide 1 3 + cSide 3 ∨ 3 * cSide 3 = 4 * bSide 1 3 ∨
      aSide 1 3 + 2 * bSide 1 3 = 2 * cSide 3) :=
  relations_fail_at_one_three

#print axioms seeddeg_rel1
#print axioms seeddeg_iff
#print axioms seeddeg_at_one_two

end Erdos634.Draft.SeedDegenerateWrap
