import Erdos634.LocalMarchRunWitness

namespace Erdos634.Draft.LocalMarchRunWitnessWrap
open Erdos634.Geometry Erdos634.CertCoord Erdos634.LocalMarchRun
open Erdos634.LocalMarchRunWitness

theorem wrap_baseRun_le_runLength :
    (4 : ℕ) ≤ Erdos634.MarchRunObject.runLength D gY 0 ‖(mkPt 16 0 : Plane)‖ :=
  baseRun_le_runLength

example : True := trivial
#print axioms wrap_baseRun_le_runLength

end Erdos634.Draft.LocalMarchRunWitnessWrap
