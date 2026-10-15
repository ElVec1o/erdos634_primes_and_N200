import Erdos634.Irregular

namespace Erdos634.Draft.IrregularWrap

open Erdos634.Irregular

theorem ir_base_beta_irregular (p : Pairing) :
    ¬ (p.equalises baseCorner ∧ p.equalises apex) :=
  base_beta_irregular p

theorem ir_which_corner_kills :
    (¬ (Pairing.ab).equalises baseCorner)
      ∧ (¬ (Pairing.ag).equalises apex)
      ∧ (¬ (Pairing.bg).equalises baseCorner) :=
  which_corner_kills

theorem ir_corner_arithmetic (x y z : ℕ) :
    (x + 2 * z = 0 → y + z = 1 → x = 0 ∧ y = 1 ∧ z = 0)
      ∧ (x + 2 * z = 3 → y + z = 0 → x = 3 ∧ y = 0 ∧ z = 0) :=
  corner_arithmetic x y z

example : ir_which_corner_kills = which_corner_kills := rfl

#print axioms ir_base_beta_irregular
#print axioms ir_corner_arithmetic

end Erdos634.Draft.IrregularWrap
