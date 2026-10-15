import Erdos634.CollarContainM4

/-!
# Containment of collar pieces in delta4

Re-exports results of `CollarContainM4`:
- `apex_subset_delta4`: the translated apex tiling target is inside `delta4`.
- `corner_subset_delta4`: the translated corner tiling target is inside `delta4`.

No `sorry`.
-/

namespace Erdos634.Draft.CollarContainM4Wrap

open Erdos634.Geometry Erdos634.CertCoord Erdos634.TranslateDissection Erdos634.CertGeom
open Erdos634.DissectionMap

/-- Wrap: the apex copy (at vertex `(88, 24√15)`) is contained in `delta4`. -/
theorem apex_subset_delta4_wrap :
    (translateCongruentDissection (mkPt 88 (24 * Real.sqrt 15))
      Erdos634.Tiling44Bridge.dissection).target.carrier ⊆ delta4.carrier :=
  apex_subset_delta4

/-- Wrap: the corner copy (at vertex `(176, 0)`) is contained in `delta4`. -/
theorem corner_subset_delta4_wrap :
    (translateCongruentDissection (mkPt 176 0)
      Erdos634.Tiling44Bridge.dissection).target.carrier ⊆ delta4.carrier :=
  corner_subset_delta4

example : True := trivial

#print axioms apex_subset_delta4_wrap
#print axioms corner_subset_delta4_wrap

end Erdos634.Draft.CollarContainM4Wrap
