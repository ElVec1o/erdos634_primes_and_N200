import Erdos634.RationalityFree

/-!
# RationalityFree — rationality-exclusion arithmetic: wrapper

Key results:
- `ratio_relation_alpha/beta`: ratio constraints from tile equations
- `product_negative`: product is positive or negative
- `degenerate_pure_c`: pure c-tiles force both multipliers to zero
- `c_rational_witness`, `three_mod_four`: witnesses

Standard axioms, no `sorry`.
-/

namespace Erdos634.Draft.RationalityFreeWrap

open Erdos634.RationalityFree

theorem rf_ratio_relation_alpha (a b N P : Int)
    (h : P * a + 2 * (P * b) = -(a * N)) :
    a * N + P * a = -(2 * (P * b)) :=
  ratio_relation_alpha a b N P h

theorem rf_ratio_relation_beta (a b N P : Int)
    (h : 2 * (P * a) + P * b = -(b * N)) :
    b * N + P * b = -(2 * (P * a)) :=
  ratio_relation_beta a b N P h

theorem rf_product_negative (a b N P : Int) (ha : 0 < a) (hN : 0 < N)
    (h : P * a + 2 * (P * b) = -(a * N)) :
    P * a < 0 ∨ P * b < 0 :=
  product_negative a b N P ha hN h

theorem rf_degenerate_pure_c (a b P Q : Int) (ha : 0 < a) (hb : 0 < b) (hP : 0 ≤ P)
    (hQ : 0 ≤ Q) (h : P * a + Q * b = 0) :
    P = 0 ∧ Q = 0 :=
  degenerate_pure_c a b P Q ha hb hP hQ h

theorem rf_c_rational_witness : (3:Int)*3 + 3*5 + 5*5 = 7*7 :=
  c_rational_witness

theorem rf_three_mod_four : (3:Int) % 4 = 3 ∧ (7:Int) % 4 = 3 :=
  three_mod_four

-- Non-vacuity
example : (3 : Int) * 3 + 3 * 5 + 5 * 5 = 7 * 7 := rf_c_rational_witness

#print axioms rf_product_negative
#print axioms rf_degenerate_pure_c

end Erdos634.Draft.RationalityFreeWrap
