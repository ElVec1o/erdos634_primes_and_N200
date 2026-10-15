import Erdos634.TriLawSin

namespace Erdos634.Draft.TriLawSinWrap
open Erdos634.Geometry Erdos634.TilePlacement Erdos634.TriLawSin

theorem wrap_b_sin_gamma_eq_c_sin_beta (T : Tri) :
    sideOpp T 1 * Real.sin (angleAt T 2) = sideOpp T 2 * Real.sin (angleAt T 1) :=
  b_sin_gamma_eq_c_sin_beta T

example : True := trivial
#print axioms wrap_b_sin_gamma_eq_c_sin_beta

end Erdos634.Draft.TriLawSinWrap
