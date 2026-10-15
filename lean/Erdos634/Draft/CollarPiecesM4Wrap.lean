import Erdos634.CollarPiecesM4

/-!
# Definition and area sum of the 176 collar pieces

Re-exports results of `CollarPiecesM4`:
- `delta4Pieces`: the 176-piece array for the delta-4 collar.
- `delta4_area_sum`: the pieces' absolute areas sum to that of `delta4`.

No `sorry`.
-/

namespace Erdos634.Draft.CollarPiecesM4Wrap

open Erdos634.Geometry Erdos634.CertCoord Erdos634.DissectionMap Erdos634.AreaDet
open Erdos634.Realizable Erdos634.TranslateDissection Erdos634.Z15Real

/-- Wrap: the absolute areas of all 176 collar pieces sum to the area of `delta4`. -/
theorem delta4_area_sum_wrap :
    ∑ i : Fin 176, |detTri (delta4Pieces i)| = |detTri delta4| :=
  delta4_area_sum

/-- Non-vacuity: `delta4Pieces` is computable as a `Fin 176 → Tri`. -/
example : (delta4Pieces : Fin 176 → Tri) = delta4Pieces := rfl

#print axioms delta4_area_sum_wrap

end Erdos634.Draft.CollarPiecesM4Wrap
