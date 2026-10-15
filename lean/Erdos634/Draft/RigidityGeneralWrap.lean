import Erdos634.RigidityGeneral

namespace Erdos634.Draft.RigidityGeneralWrap
open Erdos634.RigidityGeneral

theorem wrap_b_hits_lattice (f p : ℕ) (hf : 2 ≤ f) :
    ∃ m, p < f * m ∧ f * m < p + (f ^ 2 - 1) :=
  b_hits_lattice f p hf

example : True := trivial
#print axioms wrap_b_hits_lattice

end Erdos634.Draft.RigidityGeneralWrap
