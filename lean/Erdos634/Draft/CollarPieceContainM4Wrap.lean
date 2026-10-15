import Erdos634.CollarPieceContainM4

/-!
# Individual piece containment in delta4

Re-exports results of `CollarPieceContainM4`:
- `apexPieceAt_subset_delta4`: every apex piece is inside `delta4`.
- `cornerPieceAt_subset_delta4`: every corner piece is inside `delta4`.
- `columnPieceAt_subset_delta4`: every column piece is inside `delta4`.

No `sorry`.
-/

namespace Erdos634.Draft.CollarPieceContainM4Wrap

open Erdos634.Geometry Erdos634.CertCoord Erdos634.DissectionMap Erdos634.AreaDet
open Erdos634.Realizable Erdos634.TranslateDissection

/-- Wrap: every apex piece lies inside `delta4`. -/
theorem apexPieceAt_subset_delta4_wrap (i : Fin Tiling44.tiles.length) :
    (apexPieceAt i).carrier ⊆ delta4.carrier :=
  apexPieceAt_subset_delta4 i

/-- Wrap: every corner piece lies inside `delta4`. -/
theorem cornerPieceAt_subset_delta4_wrap (i : Fin Tiling44.tiles.length) :
    (cornerPieceAt i).carrier ⊆ delta4.carrier :=
  cornerPieceAt_subset_delta4 i

/-- Wrap: every column piece lies inside `delta4`. -/
theorem columnPieceAt_subset_delta4_wrap (j h : Fin 2) (i : Fin PgramTiling22.tiles.length) :
    (columnPieceAt (colVec j h) i).carrier ⊆ delta4.carrier :=
  columnPieceAt_subset_delta4 j h i

example : True := trivial

#print axioms apexPieceAt_subset_delta4_wrap
#print axioms cornerPieceAt_subset_delta4_wrap
#print axioms columnPieceAt_subset_delta4_wrap

end Erdos634.Draft.CollarPieceContainM4Wrap
