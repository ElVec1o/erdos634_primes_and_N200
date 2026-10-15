import Erdos634.N15IsoALift

namespace Erdos634.Draft.N15IsoALiftWrap
open Erdos634.Geometry
open Erdos634.N15IsoA

theorem wrap_not_dissection {N : ℕ} (D : CongruentDissection N)
    (hT : D.target.Congruent TGT) (hM : D.model.Congruent MODEL) : False :=
  not_dissection D hT hM

example : True := trivial
#print axioms wrap_not_dissection

end Erdos634.Draft.N15IsoALiftWrap
