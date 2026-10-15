import Erdos634.FillerGeneral

namespace Erdos634.Draft.FillerGeneralWrap
open Erdos634.FillerGeneral

theorem wrap_filler_b_general_ef {R : Type*} [CommRing R] (e f : R) :
    e ^ 2 * (f ^ 2 - e ^ 2) ^ 2 + 4 * f ^ 6 - e ^ 2 * (3 * f ^ 2 - e ^ 2) ^ 2
      = 4 * f ^ 2 * (f ^ 2 - e ^ 2) ^ 2 :=
  filler_b_general_ef e f

example : True := trivial
#print axioms wrap_filler_b_general_ef

end Erdos634.Draft.FillerGeneralWrap
