import Erdos634.GoldenForm

namespace Erdos634.Draft.GoldenFormWrap

open Erdos634.GoldenForm

theorem gf_quartic_eq_golden (e f : ℤ) :
    e ^ 4 - e ^ 3 * f - 3 * e ^ 2 * f ^ 2 + e * f ^ 3 + f ^ 4
      = b e f ^ 2 + a e f * b e f - a e f ^ 2 :=
  quartic_eq_golden e f

theorem gf_quartic_neg_iff_golden (e f : ℤ) :
    e ^ 4 - e ^ 3 * f - 3 * e ^ 2 * f ^ 2 + e * f ^ 3 + f ^ 4 < 0
      ↔ 0 < a e f ^ 2 - a e f * b e f - b e f ^ 2 :=
  quartic_neg_iff_golden e f

theorem gf_golden_form_step (a b : ℤ) :
    a ^ 2 - a * b - b ^ 2 = -(b ^ 2 - b * (a - b) - (a - b) ^ 2) :=
  golden_form_step a b

theorem gf_golden_fails_at_3_7 : a 3 7 ^ 2 - a 3 7 * b 3 7 - b 3 7 ^ 2 < 0 :=
  golden_fails_at_3_7

theorem gf_golden_holds_at_5_6 : 0 < a 5 6 ^ 2 - a 5 6 * b 5 6 - b 5 6 ^ 2 :=
  golden_holds_at_5_6

example : gf_golden_fails_at_3_7 = golden_fails_at_3_7 := rfl

#print axioms gf_quartic_eq_golden
#print axioms gf_golden_fails_at_3_7

end Erdos634.Draft.GoldenFormWrap
