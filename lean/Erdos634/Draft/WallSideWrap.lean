import Erdos634.WallSide

namespace Erdos634.Draft.WallSideWrap
open Erdos634.Geometry Erdos634.WallSide

theorem wrap_wall_edges_same_tile {N : ℕ} (D : Dissection N) (g : Plane →ᵃ[ℝ] ℝ) (c : ℝ)
    (hlin : ∃ y, g y ≠ c) (e f : Fin N × Fin 3) (hef : e ≠ f) (htile : e.1 = f.1)
    (he : g ((D.tile e.1).pts e.2) = c ∧ g ((D.tile e.1).pts (e.2 + 1)) = c)
    (hf : g ((D.tile f.1).pts f.2) = c ∧ g ((D.tile f.1).pts (f.2 + 1)) = c) : False :=
  wall_edges_same_tile D g c hlin e f hef htile he hf

example : True := trivial
#check @wrap_wall_edges_same_tile

end Erdos634.Draft.WallSideWrap
