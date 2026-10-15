import Erdos634.GeneralPillars

namespace Erdos634.Draft.GeneralPillarsWrap

open Erdos634.GeneralPillars

theorem gp_b_lattice_e2f3 (p : Nat) : ∃ m, p < 3 * m ∧ 3 * m < p + 5 :=
  b_lattice_e2f3 p

theorem gp_b_lattice_e4f5 (p : Nat) : ∃ m, p < 5 * m ∧ 5 * m < p + 9 :=
  b_lattice_e4f5 p

theorem gp_c_minus_a_undec_e2f3 : ∀ x y z : Nat, x * 6 + y * 5 + z * 9 ≠ 3 :=
  c_minus_a_undec_e2f3

theorem gp_c_minus_a_undec_e4f5 : ∀ x y z : Nat, x * 20 + y * 9 + z * 25 ≠ 5 :=
  c_minus_a_undec_e4f5

example : True := trivial

#print axioms gp_b_lattice_e2f3
#print axioms gp_c_minus_a_undec_e2f3

end Erdos634.Draft.GeneralPillarsWrap
