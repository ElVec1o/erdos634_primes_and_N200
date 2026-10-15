import Erdos634.ThickBlockingLemmas

namespace Erdos634.Draft.ThickBlockingLemmasWrap
open Erdos634.ThickBlockingLemmas
open Erdos634.Geometry Erdos634.CertCoord Erdos634.CertGeom Erdos634.BaseBetaTargetCoord

theorem wrap_B2_witness :
    w2t0.carrier ⊆ target63.carrier ∧
    w2t1.carrier ⊆ target63.carrier ∧
    w2t2.carrier ⊆ target63.carrier ∧
    w2t3.carrier ⊆ target63.carrier ∧
    w2t4.carrier ⊆ target63.carrier ∧
    w2t5.carrier ⊆ target63.carrier ∧
    Disjoint (interior w2t0.carrier) (interior w2t1.carrier) ∧
    Disjoint (interior w2t0.carrier) (interior w2t2.carrier) ∧
    Disjoint (interior w2t0.carrier) (interior w2t3.carrier) ∧
    Disjoint (interior w2t0.carrier) (interior w2t4.carrier) ∧
    Disjoint (interior w2t0.carrier) (interior w2t5.carrier) ∧
    Disjoint (interior w2t1.carrier) (interior w2t2.carrier) ∧
    Disjoint (interior w2t1.carrier) (interior w2t3.carrier) ∧
    Disjoint (interior w2t1.carrier) (interior w2t4.carrier) ∧
    Disjoint (interior w2t1.carrier) (interior w2t5.carrier) ∧
    Disjoint (interior w2t2.carrier) (interior w2t3.carrier) ∧
    Disjoint (interior w2t2.carrier) (interior w2t4.carrier) ∧
    Disjoint (interior w2t2.carrier) (interior w2t5.carrier) ∧
    Disjoint (interior w2t3.carrier) (interior w2t4.carrier) ∧
    Disjoint (interior w2t3.carrier) (interior w2t5.carrier) ∧
    Disjoint (interior w2t4.carrier) (interior w2t5.carrier) :=
  B2_witness

example : True := trivial
#print axioms wrap_B2_witness

end Erdos634.Draft.ThickBlockingLemmasWrap
