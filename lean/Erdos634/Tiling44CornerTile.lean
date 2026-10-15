import Erdos634.Tiling44Bridge

/-!
# The specific tile at `Tiling44Bridge`'s target corner `(176,0)`

`Tiling44EqualSideWalk.equal_side_walk` gives `∃ Pc Qc Rc, dist(pts1,pts2) = Pc·s₀+Qc·s₁+Rc·s₂` but
not which count is forced positive.  This file identifies the corner tile, `Tiling44.tiles[13]`,
whose vertex `1` sits exactly at `targetTri.pts 1 = (176,0)`, the wall's own start point, and checks
its two vertex-1-incident edges directly: squared lengths `256` (`= 16²`) and `1024` (`= 32²`),
never `576` (`= 24²`).  So the `b`-side (length `24`) is not incident to this corner; the two edges
leaving the corner are the `a`-side (`16`) and the `c`-side (`32`).

No `sorry`; standard axioms only.
-/

open Erdos634.Tiling44Bridge

/-- Tile `13`'s vertex `1` is exactly the target's corner `(176,0)` — the wall's own start point. -/
theorem corner_tile_vertex : vertexOf Tiling44.tiles[13] 1 = (176, 0, 0, 0) := by decide

/-- The edge from the corner to `Tiling44.tiles[13]`'s vertex `0` has squared length `256 = 16²`
— the model's `a`-side. -/
theorem corner_tile_edge_a :
    Tiling44.dist2 (Tiling44.t2 Tiling44.tiles[13]) (Tiling44.t1 Tiling44.tiles[13])
      = (256, 0) := by decide

/-- The edge from the corner to `Tiling44.tiles[13]`'s vertex `2` has squared length `1024 = 32²`
— the model's `c`-side. -/
theorem corner_tile_edge_c :
    Tiling44.dist2 (Tiling44.t2 Tiling44.tiles[13]) (Tiling44.t3 Tiling44.tiles[13])
      = (1024, 0) := by decide
