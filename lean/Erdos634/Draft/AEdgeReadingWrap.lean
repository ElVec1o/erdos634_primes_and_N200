import Erdos634.AEdgeReading

namespace Erdos634.Draft.AEdgeReadingWrap
open Erdos634.AEdgeReading
open Erdos634.Geometry Erdos634.Placement Erdos634.Inflation Erdos634.TilePlacement

variable {N : ℕ}

/-- West and east local angles of a real a-edge are {β,γ} in opposite order. -/
theorem wrap_a_edge_west_east (D : CongruentDissection N) (α β γ : ℝ)
    (hα' : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hβ' : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hγ' : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    (hscalene : ∀ m m' : Fin 3, m ≠ m' → sideOpp D.model m ≠ sideOpp D.model m')
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hβγ : β ≠ γ)
    (dir : Plane →ₗ[ℝ] ℝ) (i : Fin N) (k : Fin 3)
    (hlen : dist ((D.tile i).pts k) ((D.tile i).pts (k + 1)) = sideOpp D.model 0) :
    ((D.tile i).localAngle (edgeWest D.toDissection dir (i, k)) = β ∨
      (D.tile i).localAngle (edgeWest D.toDissection dir (i, k)) = γ) ∧
    ((D.tile i).localAngle (edgeEast D.toDissection dir (i, k)) = β ∨
      (D.tile i).localAngle (edgeEast D.toDissection dir (i, k)) = γ) ∧
    (D.tile i).localAngle (edgeWest D.toDissection dir (i, k)) ≠
      (D.tile i).localAngle (edgeEast D.toDissection dir (i, k)) :=
  a_edge_west_east D α β γ hα' hβ' hγ' hscalene hαβ hαγ hβγ dir i k hlen

example : True := trivial

#print axioms wrap_a_edge_west_east

end Erdos634.Draft.AEdgeReadingWrap
