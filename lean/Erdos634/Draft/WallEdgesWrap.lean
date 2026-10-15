import Erdos634.WallEdges

namespace Erdos634.Draft.WallEdgesWrap
open Erdos634.WallEdges Erdos634.Geometry

theorem wrap_base_covered_by_wall_edges {N : ℕ} (D : Dissection N) (g : Plane →ᵃ[ℝ] ℝ) (c : ℝ)
    (hwall : ∀ y ∈ D.target.carrier, g y ≤ c) (a b : Plane) (hab : a ≠ b)
    (hbase : segment ℝ a b ⊆ frontier D.target.carrier)
    (hline : ∀ y ∈ segment ℝ a b, g y = c) :
    segment ℝ a b ⊆ ⋃ p ∈ {p : Fin N × Fin 3 | WallEdge D g c p}, (D.tile p.1).edge p.2 :=
  base_covered_by_wall_edges D g c hwall a b hab hbase hline

example : True := trivial
#print axioms wrap_base_covered_by_wall_edges

end Erdos634.Draft.WallEdgesWrap
