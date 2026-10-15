import Erdos634.ResidueRunZ1

namespace Erdos634.Draft.ResidueRunZ1Wrap
open Erdos634.ResidueRunZ1 Erdos634.CertCoord Erdos634.ThickBlockingLemmas

theorem wrap_Z1run_witness :
    z1t5.carrier ⊆ target63.carrier ∧ z1t17.carrier ⊆ target63.carrier ∧
    Disjoint (interior z1t5.carrier) (interior z1t17.carrier) ∧
    z1t5.pts 2 = mkPt (14 : ℝ) ((1 : ℝ)*rr) ∧
    z1t17.pts 2 = mkPt (46/3 : ℝ) ((5/3 : ℝ)*rr) ∧
    (5/2 : ℝ)*rr*(46/3 : ℝ) - 23*((5/3 : ℝ)*rr) = 0 :=
  Z1run_witness

example : True := trivial
#print axioms wrap_Z1run_witness

end Erdos634.Draft.ResidueRunZ1Wrap
