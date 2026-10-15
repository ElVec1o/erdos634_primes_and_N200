import Erdos634.MarchRunObject
namespace Erdos634.Draft.MarchRunObjectWrap
open Erdos634.MarchRunObject
open Erdos634.Geometry

theorem wrap_aRun_nodup {N : ℕ} (D : Dissection N) (g : Plane →ᵃ[ℝ] ℝ) (c a : ℝ) :
    (aRun D g c a).Nodup :=
  aRun_nodup D g c a

theorem wrap_mem_aRun {N : ℕ} (D : Dissection N) (g : Plane →ᵃ[ℝ] ℝ) (c a : ℝ)
    (p : Fin N × Fin 3) :
    p ∈ aRun D g c a ↔
      (Erdos634.WallEdges.WallEdge D g c p ∧
        dist ((D.tile p.1).pts p.2) ((D.tile p.1).pts (p.2 + 1)) = a) :=
  mem_aRun D g c a p

theorem wrap_runTile_spec {N : ℕ} (D : Dissection N) (g : Plane →ᵃ[ℝ] ℝ) (c a : ℝ)
    (i : Fin (runLength D g c a)) :
    Erdos634.WallEdges.WallEdge D g c (runTile D g c a i, runEdge D g c a i) ∧
      dist ((D.tile (runTile D g c a i)).pts (runEdge D g c a i))
        ((D.tile (runTile D g c a i)).pts (runEdge D g c a i + 1)) = a :=
  runTile_spec D g c a i

theorem wrap_run_exceptional_le_one {N : ℕ} (D : Dissection N) (g : Plane →ᵃ[ℝ] ℝ) (c a : ℝ)
    (w : ℕ → Bool)
    (hmono : ∀ i, i + 1 < runLength D g c a → w i = true → w (i + 1) = true) :
    ((Finset.range (runLength D g c a)).filter
      (fun i => i + 1 < runLength D g c a ∧ w i ≠ w (i + 1))).card ≤ 1 :=
  run_exceptional_le_one D g c a w hmono

example : True := trivial
#print axioms wrap_aRun_nodup
#print axioms wrap_run_exceptional_le_one
end Erdos634.Draft.MarchRunObjectWrap
