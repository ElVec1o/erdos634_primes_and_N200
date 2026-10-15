import Erdos634.CollarDisjointColM4

/-!
# Disjointness between different column blocks

Re-exports `CollarDisjointColM4.columnPieceAt_disjoint`: pieces from distinct column positions
`(j,h) ≠ (j',h')` have disjoint interiors.

No `sorry`.
-/

namespace Erdos634.Draft.CollarDisjointColM4Wrap

open Erdos634.Geometry Erdos634.CertCoord Erdos634.DissectionMap Erdos634.CertGeom
open Erdos634.Realizable Erdos634.TranslateDissection

/-- Wrap: pieces from distinct column-grid positions have disjoint interiors. -/
theorem columnPieceAt_disjoint_wrap (j h j' h' : Fin 2)
    (i i' : Fin PgramTiling22.tiles.length) (hne : (j, h) ≠ (j', h')) :
    Disjoint (interior (columnPieceAt (colVec j h) i).carrier)
      (interior (columnPieceAt (colVec j' h') i').carrier) :=
  columnPieceAt_disjoint j h j' h' i i' hne

example : True := trivial

#print axioms columnPieceAt_disjoint_wrap

end Erdos634.Draft.CollarDisjointColM4Wrap
