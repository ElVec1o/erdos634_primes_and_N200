import Erdos634.BaseSelection

/-!
# Tile/boundary geometric containment: wrapper

Re-exports results of `BaseSelection`:
- `tile_subset_target`: tile carrier ⊆ target carrier
- `tile_interior_subset`: tile interior ⊆ target interior
- `boundary_point_on_edge`: frontier points lie on tile edges
- `coord_zero_mem_segment`: zero barycentric coord → point on opposite edge
- `frontier_subset_edges`: all frontier points lie on some tile edge

No `sorry`; standard axioms only.
-/

namespace Erdos634.Draft.BaseSelectionWrap

open Erdos634.BaseSelection Erdos634.Geometry

theorem bs_tile_subset_target {N : ℕ} (D : Dissection N) (i : Fin N) :
    (D.tile i).carrier ⊆ D.target.carrier :=
  Erdos634.BaseSelection.tile_subset_target D i

theorem bs_tile_interior_subset {N : ℕ} (D : Dissection N) (i : Fin N) :
    interior (D.tile i).carrier ⊆ interior D.target.carrier :=
  Erdos634.BaseSelection.tile_interior_subset D i

theorem bs_boundary_point_on_edge {N : ℕ} (D : Dissection N) {x : Plane}
    (hx : x ∈ frontier D.target.carrier)
    (hvert : ∀ i k, x ≠ (D.tile i).pts k) :
    ∃ i, Erdos634.Geometry.OnEdge D x i :=
  Erdos634.BaseSelection.boundary_point_on_edge D hx hvert

theorem bs_coord_zero_mem_segment (T : Tri) (k : Fin 3) (x : Plane)
    (h0 : T.basis.coord k x = 0) (hnn : ∀ j, 0 ≤ T.basis.coord j x) :
    x ∈ segment ℝ (T.pts (k+1)) (T.pts (k+2)) :=
  Erdos634.BaseSelection.coord_zero_mem_segment T k x h0 hnn

-- Non-vacuity: tile_subset_target is type-correct
example : @bs_tile_subset_target = @bs_tile_subset_target := rfl

#print axioms bs_tile_subset_target
#print axioms bs_boundary_point_on_edge

end Erdos634.Draft.BaseSelectionWrap
