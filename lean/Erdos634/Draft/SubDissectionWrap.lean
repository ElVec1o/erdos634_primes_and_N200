import Erdos634.SubDissection

/-!
# SubDissection: sub-region restriction of a dissection

`SubDissection.restrict` (and `restrictCongruent`) build a sub-dissection from a
subset of tiles whose union equals a given triangle.

0 sorry, standard axioms.
-/

namespace Erdos634.Draft.SubDissectionWrap

open Erdos634.SubDissection Erdos634.Geometry

theorem subdissection_restrict_target (N : ℕ) (D : Dissection N) (S : Finset (Fin N)) (T : Tri)
    (hcov : (⋃ i ∈ S, (D.tile i).carrier) = T.carrier) :
    (restrict D S T hcov).target = T :=
  restrict_target D S T hcov

theorem subdissection_restrictCongruent_target (N : ℕ) (D : CongruentDissection N)
    (S : Finset (Fin N)) (T : Tri)
    (hcov : (⋃ i ∈ S, (D.tile i).carrier) = T.carrier) :
    (restrictCongruent D S T hcov).target = T :=
  restrictCongruent_target D S T hcov

theorem subdissection_restrictCongruent_model (N : ℕ) (D : CongruentDissection N)
    (S : Finset (Fin N)) (T : Tri)
    (hcov : (⋃ i ∈ S, (D.tile i).carrier) = T.carrier) :
    (restrictCongruent D S T hcov).model = D.model :=
  restrictCongruent_model D S T hcov

#print axioms subdissection_restrict_target
#print axioms subdissection_restrictCongruent_target
#print axioms subdissection_restrictCongruent_model

end Erdos634.Draft.SubDissectionWrap
