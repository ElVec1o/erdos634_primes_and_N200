import Erdos634.PgramTiling52Bridge
import Erdos634.RegionDissection

/-!
# `PgramTiling52Bridge` as a `CongruentRegionDissection`

`PgramTiling52Bridge` has no `CongruentDissection` object — its target is a parallelogram carrier
(`convexHull ℝ {v1,v2,v3,v4}`), not a `Tri`, so `Dissection`'s `Tri`-typed target can't express it.
`RegionDissection` (built to close exactly this kind of gap) can. Every ingredient already exists:
`pgram52_covers` (the 52 pieces' union is the carrier), `pieces_interiors_disjoint`, and
`pieceTri_congruent` (every piece congruent to the model). This file assembles them.

This is the f=3 analogue of `PgramTiling22Region`. Both are used as building blocks in the
collar induction for `prop:widecol` / `thm:pgram-e1`.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.PgramTiling52Region

open Erdos634.Geometry Erdos634.RegionDissection

/-- `PgramTiling52Bridge`'s 52 pieces, as a `CongruentRegionDissection` of the parallelogram
carrier (f=3, tile (3,8,9)). -/
noncomputable def dissection : CongruentRegionDissection PgramTiling52.tiles.length where
  region := Erdos634.PgramTiling52Bridge.carrier
  tile := Erdos634.PgramTiling52Bridge.pieceAt
  covers := Erdos634.PgramTiling52Bridge.pgram52_covers
  interiors_disjoint := fun i j hij =>
    Erdos634.PgramTiling52Bridge.pieces_interiors_disjoint
      (List.getElem_mem i.isLt) (List.getElem_mem j.isLt)
      (Erdos634.PgramTiling52Bridge.tiles_getElem_inj i j hij)
  model := Erdos634.PgramTiling52Bridge.pieceTri Erdos634.PgramTiling52Bridge.headI_mem_tiles
  tiles_congruent := fun i =>
    Erdos634.PgramTiling52Bridge.pieceTri_congruent (List.getElem_mem i.isLt)

end Erdos634.PgramTiling52Region
