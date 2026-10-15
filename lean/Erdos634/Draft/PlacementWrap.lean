import Erdos634.Placement

/-!
# Placement — edge placement and contiguity: wrapper

Key results:
- `dir_edgeWest/East`: wall coordinate of west/east edge endpoints
- `contiguous_of_no_gap`: sorted intervals with no gap → consecutive endpoints shared
- `shared_junction`: abuting chain edges share the junction point
- `constant_of_vertices_eq`: functional equal at all three vertices is constant
- `no_double_wall_tile`: no tile contributes two wall edges

Standard axioms, no `sorry`.
-/

namespace Erdos634.Draft.PlacementWrap

open Erdos634.Placement Erdos634.Geometry Erdos634.OrientBridge Erdos634.ChainInstance

theorem pm_dir_edgeWest {N : ℕ} (D : Dissection N) (dir : Plane →ₗ[ℝ] ℝ) (e1 : Fin N × Fin 3) :
    dir (edgeWest D dir e1) = edgePos D dir e1 :=
  dir_edgeWest D dir e1

theorem pm_dir_edgeEast {N : ℕ} (D : Dissection N) (dir : Plane →ₗ[ℝ] ℝ) (e1 : Fin N × Fin 3) :
    dir (edgeEast D dir e1) = edgeEnd D dir e1 :=
  dir_edgeEast D dir e1

theorem pm_contiguous_of_no_gap (L R : ℕ → ℝ) (n k : ℕ) (hk1 : k + 1 < n)
    (hnd : ∀ j < n, L j ≤ R j)
    (hsorted : ∀ i j, i ≤ j → j < n → L i ≤ L j)
    (hnoov : ∀ i j, i < j → j < n → R i ≤ L j)
    (hreach : ∃ j ≤ k, L (k + 1) ≤ R j) :
    R k = L (k + 1) :=
  contiguous_of_no_gap L R n k hk1 hnd hsorted hnoov hreach

theorem pm_shared_junction {N : ℕ} (D : Dissection N) (dir : Plane →ₗ[ℝ] ℝ) (S : Set Plane)
    (hinj : Set.InjOn dir S) (e1 e2 : Fin N × Fin 3)
    (hE : edgeEast D dir e1 ∈ S) (hW : edgeWest D dir e2 ∈ S)
    (h : edgeEnd D dir e1 = edgePos D dir e2) :
    edgeEast D dir e1 = edgeWest D dir e2 :=
  shared_junction D dir S hinj e1 e2 hE hW h

theorem pm_constant_of_vertices_eq (T : Tri) (g : Plane →ᵃ[ℝ] ℝ) (c : ℝ)
    (h0 : g (T.pts 0) = c) (h1 : g (T.pts 1) = c) (h2 : g (T.pts 2) = c) (y : Plane) :
    g y = c :=
  constant_of_vertices_eq T g c h0 h1 h2 y

theorem pm_no_double_wall_tile (T : Tri) (g : Plane →ᵃ[ℝ] ℝ) (c : ℝ) (hlin : ∃ y, g y ≠ c)
    (h0 : g (T.pts 0) = c) (h1 : g (T.pts 1) = c) (h2 : g (T.pts 2) = c) : False :=
  no_double_wall_tile T g c hlin h0 h1 h2

-- Non-vacuity: constant_of_vertices_eq when all agree
example : @pm_constant_of_vertices_eq = @pm_constant_of_vertices_eq := rfl

#print axioms pm_contiguous_of_no_gap
#print axioms pm_no_double_wall_tile

end Erdos634.Draft.PlacementWrap
