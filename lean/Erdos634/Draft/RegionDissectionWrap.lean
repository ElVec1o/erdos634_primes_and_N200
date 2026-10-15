import Erdos634.RegionDissection

namespace Erdos634.Draft.RegionDissectionWrap
open Erdos634.Geometry Erdos634.RegionDissection

theorem wrap_restrictCongruent_model {N : ℕ} (C : CongruentRegionDissection N)
    (S : Finset (Fin N)) (region' : Set Plane)
    (hcov : (⋃ i ∈ S, (C.tile i).carrier) = region') :
    (restrictCongruent C S region' hcov).model = C.model :=
  restrictCongruent_model C S region' hcov

example : True := trivial
#print axioms wrap_restrictCongruent_model

end Erdos634.Draft.RegionDissectionWrap
