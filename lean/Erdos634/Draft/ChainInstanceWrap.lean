import Erdos634.ChainInstance
namespace Erdos634.Draft.ChainInstanceWrap
open Erdos634.ChainInstance Erdos634.Geometry Erdos634.OrientBridge Set

theorem wrap_edge_image_eq_uIcc (T : Tri) (i : Fin 3) (dir : Plane →ₗ[ℝ] ℝ) :
    dir '' (T.edge i) = uIcc (dir (T.pts i)) (dir (T.pts (i + 1))) :=
  edge_image_eq_uIcc T i dir

theorem wrap_edgePos_le_edgeEnd {N : ℕ} (D : Dissection N) (dir : Plane →ₗ[ℝ] ℝ)
    (e : Fin N × Fin 3) : edgePos D dir e ≤ edgeEnd D dir e :=
  edgePos_le_edgeEnd D dir e

theorem wrap_consecutive_edges_meet {N : ℕ} (D : Dissection N) (dir : Plane →ₗ[ℝ] ℝ)
    (n : ℕ) (E : ℕ → Fin N × Fin 3) (a b : ℝ) (k : ℕ) (hk1 : k + 1 < n)
    (hcov : Icc a b ⊆ ⋃ j ∈ Finset.range n, dir '' ((D.tile (E j).1).edge (E j).2))
    (hsub : ∀ j, j < n → dir '' ((D.tile (E j).1).edge (E j).2) ⊆ Icc a b)
    (hsorted : ∀ i j, i ≤ j → j < n → edgePos D dir (E i) ≤ edgePos D dir (E j)) :
    ∃ j ≤ k, edgePos D dir (E (k + 1)) ≤ edgeEnd D dir (E j) :=
  consecutive_edges_meet D dir n E a b k hk1 hcov hsub hsorted

example : True := trivial
#print axioms wrap_consecutive_edges_meet
end Erdos634.Draft.ChainInstanceWrap
