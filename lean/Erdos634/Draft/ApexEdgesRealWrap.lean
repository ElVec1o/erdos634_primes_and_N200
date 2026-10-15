import Erdos634.ApexEdgesReal

/-!
# Corner tile base edge: wrapper

`ApexEdgesReal.congruentDissection_apex_edges` shows that at a corner vertex
(angle = 3α) a tile with local angle α has its vertex there, and the two
adjacent edges have the model's b- and c-lengths in some order.

No `sorry`; standard axioms only.
-/

namespace Erdos634.Draft.ApexEdgesRealWrap

open Erdos634.ApexEdgesReal Erdos634.Geometry Erdos634.TilePlacement

theorem apex_edges_real {N : ℕ} (D : CongruentDissection N) (α β γ : ℝ)
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hαπ : α ≠ Real.pi) (hα0 : α ≠ 0) (hα2π : α ≠ 2 * Real.pi)
    (hβγ : β ≠ γ)
    (hγdef : γ = 2 * α + β) (hrel : 3 * α + 2 * β = Real.pi)
    (hα' : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hβ' : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hγ' : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    (hc : sideOpp D.model 0 ≠ 0)
    (k : Fin 3)
    (hcorner : cornerAngle (D.target.pts (k + 1)) (D.target.pts k) (D.target.pts (k + 2)) = 3 * α)
    (i : Fin N) (hi : (D.tile i).localAngle (D.target.pts k) = α) :
    ∃ j : Fin 3, D.target.pts k = (D.tile i).pts j ∧
      ((dist ((D.tile i).pts j) ((D.tile i).pts (j+1)) = sideOpp D.model 1 ∧
        dist ((D.tile i).pts (j+2)) ((D.tile i).pts j) = sideOpp D.model 2) ∨
       (dist ((D.tile i).pts j) ((D.tile i).pts (j+1)) = sideOpp D.model 2 ∧
        dist ((D.tile i).pts (j+2)) ((D.tile i).pts j) = sideOpp D.model 1)) :=
  congruentDissection_apex_edges D α β γ hαβ hαγ hαπ hα0 hα2π hβγ
    hγdef hrel hα' hβ' hγ' hc k hcorner i hi

#print axioms apex_edges_real

end Erdos634.Draft.ApexEdgesRealWrap
