import Erdos634.CollarDisjointM4

/-!
# Disjointness between apex, corner, and column regions

Re-exports results of `CollarDisjointM4`:
- `apex_corner_disjoint`: the apex and corner translated tilings have disjoint interiors.
- `translated_tiling44_interiors_disjoint`: tiles within a single translated Tiling44 are pairwise disjoint.

No `sorry`.
-/

namespace Erdos634.Draft.CollarDisjointM4Wrap

open Erdos634.Geometry Erdos634.CertCoord Erdos634.TranslateDissection Erdos634.CertGeom
open Erdos634.DissectionMap

/-- Wrap: the apex and corner tiling regions have disjoint interiors. -/
theorem apex_corner_disjoint_wrap :
    Disjoint (interior (translateCongruentDissection (mkPt 88 (24 * Real.sqrt 15))
        Erdos634.Tiling44Bridge.dissection).target.carrier)
      (interior (translateCongruentDissection (mkPt 176 0)
        Erdos634.Tiling44Bridge.dissection).target.carrier) :=
  apex_corner_disjoint

/-- Wrap: tiles within any translated Tiling44 copy have pairwise disjoint interiors. -/
theorem translated_tiling44_interiors_disjoint_wrap (v : Plane)
    {i j : Fin Tiling44.tiles.length} (hij : i ≠ j) :
    Disjoint (interior ((translateCongruentDissection v
        Erdos634.Tiling44Bridge.dissection).tile i).carrier)
      (interior ((translateCongruentDissection v
        Erdos634.Tiling44Bridge.dissection).tile j).carrier) :=
  translated_tiling44_interiors_disjoint v hij

example : True := trivial

#print axioms apex_corner_disjoint_wrap
#print axioms translated_tiling44_interiors_disjoint_wrap

end Erdos634.Draft.CollarDisjointM4Wrap
