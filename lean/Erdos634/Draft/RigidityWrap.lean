import Erdos634.Rigidity

namespace Erdos634.Draft.RigidityWrap
open Erdos634.Rigidity

theorem wrap_b_hits_lattice_f12 (p : Nat) : ∃ m, p < 12*m ∧ 12*m < p + 143 :=
  b_hits_lattice_f12 p

example : True := trivial
#print axioms wrap_b_hits_lattice_f12

end Erdos634.Draft.RigidityWrap
