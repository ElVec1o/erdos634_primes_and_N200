import Erdos634.TileAdjacency

namespace Erdos634.Draft.TileAdjacencyWrap
open Erdos634.TileAdjacency
open Erdos634.Geometry Erdos634.Geometry.Dissection

theorem wrap_exists_unique_other_tile {N : ℕ} (D : Dissection N) (hN : 0 < N) {x : Plane}
    (hxv : ∀ i k, x ≠ (D.tile i).pts k)
    {R : ℝ} (hR : 0 < R) (hRt : Metric.ball x R ⊆ D.target.carrier)
    (i : Fin N) (hi : OnEdge D x i) :
    ∃! j : Fin N, j ≠ i ∧ OnEdge D x j :=
  exists_unique_other_tile D hN hxv hR hRt i hi

example : True := trivial
#check @wrap_exists_unique_other_tile

end Erdos634.Draft.TileAdjacencyWrap
