import Erdos634.BEdgeReading

namespace Erdos634.Draft.BEdgeReadingWrap

open Erdos634.BEdgeReading
open Erdos634.Geometry Erdos634.Placement Erdos634.Inflation Erdos634.TilePlacement
open Erdos634.OrientWord Erdos634.BridgeC Erdos634.WallEndpoints

-- Re-exports: orientation word read off a real b-edge (thm:chain)

theorem wrap_b_edge_west_east {N : ℕ} (D : CongruentDissection N) (α β γ : ℝ)
    (hα' : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hβ' : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hγ' : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    (hscalene : ∀ m m' : Fin 3, m ≠ m' → sideOpp D.model m ≠ sideOpp D.model m')
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hβγ : β ≠ γ)
    (dir : Plane →ₗ[ℝ] ℝ) (i : Fin N) (k : Fin 3)
    (hlen : dist ((D.tile i).pts k) ((D.tile i).pts (k + 1)) = sideOpp D.model 1) :
    ((D.tile i).localAngle (edgeWest D.toDissection dir (i, k)) = α ∨
      (D.tile i).localAngle (edgeWest D.toDissection dir (i, k)) = γ) ∧
    ((D.tile i).localAngle (edgeEast D.toDissection dir (i, k)) = α ∨
      (D.tile i).localAngle (edgeEast D.toDissection dir (i, k)) = γ) ∧
    (D.tile i).localAngle (edgeWest D.toDissection dir (i, k)) ≠
      (D.tile i).localAngle (edgeEast D.toDissection dir (i, k)) :=
  b_edge_west_east D α β γ hα' hβ' hγ' hscalene hαβ hαγ hβγ dir i k hlen

theorem wrap_tile_orient_BG_east_gamma {N : ℕ} (D : CongruentDissection N) (α β γ : ℝ)
    (hα' : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hβ' : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hγ' : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    (hscalene : ∀ m m' : Fin 3, m ≠ m' → sideOpp D.model m ≠ sideOpp D.model m')
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hβγ : β ≠ γ)
    (dir : Plane →ₗ[ℝ] ℝ) (i : Fin N) (k : Fin 3)
    (hlen : dist ((D.tile i).pts k) ((D.tile i).pts (k + 1)) = sideOpp D.model 1)
    (h : Erdos634.OrientBridge.tileOrient D.toDissection α i
      (edgeWest D.toDissection dir (i, k)) = Orient.BG) :
    (D.tile i).localAngle (edgeEast D.toDissection dir (i, k)) = γ :=
  tile_orient_BG_east_gamma D α β γ hα' hβ' hγ' hscalene hαβ hαγ hβγ dir i k hlen h

theorem wrap_tile_orient_GB_west_gamma {N : ℕ} (D : CongruentDissection N) (α β γ : ℝ)
    (hα' : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hβ' : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hγ' : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    (hscalene : ∀ m m' : Fin 3, m ≠ m' → sideOpp D.model m ≠ sideOpp D.model m')
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hβγ : β ≠ γ)
    (dir : Plane →ₗ[ℝ] ℝ) (i : Fin N) (k : Fin 3)
    (hlen : dist ((D.tile i).pts k) ((D.tile i).pts (k + 1)) = sideOpp D.model 1)
    (h : Erdos634.OrientBridge.tileOrient D.toDissection α i
      (edgeWest D.toDissection dir (i, k)) = Orient.GB) :
    (D.tile i).localAngle (edgeWest D.toDissection dir (i, k)) = γ :=
  tile_orient_GB_west_gamma D α β γ hα' hβ' hγ' hscalene hαβ hαγ hβγ dir i k hlen h

example : True := trivial

#print axioms Erdos634.BEdgeReading.b_edge_west_east
#print axioms Erdos634.BEdgeReading.tile_orient_BG_east_gamma

end Erdos634.Draft.BEdgeReadingWrap
