import Erdos634.CornerBaseEdgesReal

/-!
# CornerBaseEdgesReal: corner tile base-edge theorem, wrapper

`CornerBaseEdgesReal.congruentDissection_base_corner_edges`: at a β-corner vertex k,
there exists a tile with one edge along each of the two target sides from k,
with lengths a (=sideOpp 0) and c (=sideOpp 2).

This is the "corner tile's base edge" result.

No sorry, standard axioms.
-/

namespace Erdos634.Draft.CornerBaseEdgesRealWrap

open Erdos634.CornerBaseEdgesReal Erdos634.Geometry Erdos634.TilePlacement

theorem base_corner_edges {N : ℕ} (D : CongruentDissection N) (α β γ : ℝ)
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hαπ : α ≠ Real.pi) (hα0 : α ≠ 0)
    (hβγ : β ≠ γ) (hβπ : β ≠ Real.pi) (hβ0 : β ≠ 0) (hβ2π : β ≠ 2 * Real.pi)
    (hγπ : γ ≠ Real.pi) (hγ0 : γ ≠ 0) (hπ0 : Real.pi ≠ 0)
    (hγdef : γ = 2 * α + β) (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (hα' : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hβ' : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hγ' : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    (hb : sideOpp D.model 1 ≠ 0)
    (k : Fin 3)
    (hcorner : cornerAngle (D.target.pts (k + 1)) (D.target.pts k) (D.target.pts (k + 2)) = β) :
    ∃ i : Fin N, ∃ j : Fin 3, D.target.pts k = (D.tile i).pts j ∧
      ((dist ((D.tile i).pts j) ((D.tile i).pts (j+1)) = sideOpp D.model 2 ∧
        dist ((D.tile i).pts (j+2)) ((D.tile i).pts j) = sideOpp D.model 0) ∨
       (dist ((D.tile i).pts j) ((D.tile i).pts (j+1)) = sideOpp D.model 0 ∧
        dist ((D.tile i).pts (j+2)) ((D.tile i).pts j) = sideOpp D.model 2)) :=
  congruentDissection_base_corner_edges D α β γ hαβ hαγ hαπ hα0 hβγ hβπ hβ0 hβ2π
    hγπ hγ0 hπ0 hγdef hrel hirr hα' hβ' hγ' hb k hcorner

#print axioms base_corner_edges

end Erdos634.Draft.CornerBaseEdgesRealWrap
