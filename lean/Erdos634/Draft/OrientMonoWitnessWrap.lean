import Erdos634.OrientMonoWitness

namespace Erdos634.Draft.OrientMonoWitnessWrap
open Erdos634.Geometry Erdos634.CertCoord Erdos634.DissectionMap
open Erdos634.TranslateDissection Erdos634.OrientMonoWitness

theorem wrap_corner_covers :
    (⋃ i ∈ cornerIndices, (delta4CongruentDissection.tile i).carrier)
      = (mapTri (transEquiv (mkPt 176 0)).toAffineEquiv
          Erdos634.Tiling44Bridge.targetTri).carrier :=
  corner_covers

example : True := trivial
#print axioms wrap_corner_covers

end Erdos634.Draft.OrientMonoWitnessWrap
