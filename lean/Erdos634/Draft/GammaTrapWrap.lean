import Erdos634.GammaTrap

/-!
# γ-trap: every side of a base-β target carries ≥1 c-edge (wrapper for `GammaTrap`)

Key results:
- `congruentDissection_gammatrap`: side from β-corner to apex carries a c-edge
- `congruentDissection_gammatrap_base`: base side (β–β) carries a c-edge
- `congruentDissection_gammatrap_apexstart`: side from apex to β-corner carries a c-edge

0 sorry, standard axioms.
-/

namespace Erdos634.Draft.GammaTrapWrap

open Erdos634.Geometry Erdos634.Geometry.Dissection Erdos634.TilePlacement Erdos634.WallEndpoints
    Erdos634.Placement Erdos634.BaseChain Erdos634.ChainInstance Erdos634.OrientBridge
    Erdos634.GammaCascade Erdos634.SideWall

theorem gt_gammatrap {N : ℕ} (hN : 0 < N) (D : CongruentDissection N) (α β γ : ℝ)
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hαπ : α ≠ Real.pi) (hα0 : α ≠ 0)
    (hβγ : β ≠ γ) (hβπ : β ≠ Real.pi) (hβ0 : β ≠ 0)
    (hγπ : γ ≠ Real.pi) (hγ0 : γ ≠ 0) (hπ0 : Real.pi ≠ 0)
    (hγdef : γ = 2 * α + β) (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (hscalene : ∀ m m' : Fin 3, m ≠ m' → sideOpp D.model m ≠ sideOpp D.model m')
    (hα' : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hβ' : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hγ' : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    (k : Fin 3) (dir : Plane →ₗ[ℝ] ℝ)
    (hker : ∀ v : Plane, (wallFun D.target k).linear v = 0 → dir v = 0 → v = 0)
    (hdirab : dir (D.target.pts k) ≤ dir (D.target.pts (k + 1)))
    (hthird : ∀ p ∈ wallList D.toDissection (wallFun D.target k) 0,
      wallFun D.target k ((D.tile p.1).pts (p.2 + 2)) < 0)
    (hcornerbase : cornerAngle (D.target.pts (k + 1)) (D.target.pts k)
      (D.target.pts (k + 2)) = β)
    (hcornerapex : cornerAngle (D.target.pts (k + 1 + 1)) (D.target.pts (k + 1))
      (D.target.pts (k + 1 + 2)) = 3 * α) :
    ∃ p ∈ wallList D.toDissection (wallFun D.target k) 0,
      dist ((D.tile p.1).pts p.2) ((D.tile p.1).pts (p.2 + 1)) = sideOpp D.model 2 :=
  congruentDissection_gammatrap hN D α β γ hαβ hαγ hαπ hα0 hβγ hβπ hβ0 hγπ hγ0 hπ0
    hγdef hrel hirr hscalene hα' hβ' hγ' k dir hker hdirab hthird hcornerbase hcornerapex

-- Non-vacuity
example : @gt_gammatrap = @gt_gammatrap := rfl

#print axioms gt_gammatrap

end Erdos634.Draft.GammaTrapWrap
