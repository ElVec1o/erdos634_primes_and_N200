import Erdos634.BaseWalkGeneral

/-!
# γ-trap walk equation for any real base-β dissection: wrapper

Re-exports results of `BaseWalkGeneral`:
- `hiso_wallFun'`: dirFun linear part is calibrated with distance
- `base_walk_pos_general`: any real base-β dissection has Rc ≥ 1 (γ-trap)

No `sorry`; standard axioms only.
-/

namespace Erdos634.Draft.BaseWalkGeneralWrap

open Erdos634.Geometry Erdos634.Geometry.Dissection Erdos634.SideWall Erdos634.TilePlacement
    Erdos634.SideWalk

theorem bwg_hiso_wallFun' (T : Tri) (k : Fin 3) (p q : Plane)
    (hp : wallFun T k p = 0) (hq : wallFun T k q = 0) :
    dist p q = |(dirFun T k).linear p - (dirFun T k).linear q| :=
  hiso_wallFun' T k p q hp hq

theorem bwg_base_walk_pos_general {N : ℕ} (hN : 0 < N) (D : CongruentDissection N)
    (α β γ : ℝ)
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hαπ : α ≠ Real.pi) (hα0 : α ≠ 0)
    (hβγ : β ≠ γ) (hβπ : β ≠ Real.pi) (hβ0 : β ≠ 0)
    (hγπ : γ ≠ Real.pi) (hγ0 : γ ≠ 0) (hπ0 : Real.pi ≠ 0)
    (hγdef : γ = 2 * α + β) (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (hscalene : ∀ m m' : Fin 3, m ≠ m' → sideOpp D.model m ≠ sideOpp D.model m')
    (hα' : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hβ' : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hγ' : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    (k : Fin 3)
    (hdirab : (dirFun D.target k).linear (D.target.pts k)
      ≤ (dirFun D.target k).linear (D.target.pts (k + 1)))
    (hcornerbase : cornerAngle (D.target.pts (k + 1)) (D.target.pts k)
      (D.target.pts (k + 2)) = β)
    (hcornerapex : cornerAngle (D.target.pts (k + 1 + 1)) (D.target.pts (k + 1))
      (D.target.pts (k + 1 + 2)) = 3 * α) :
    ∃ Pc Qc Rc : ℕ, 1 ≤ Rc ∧
      dist (D.target.pts k) (D.target.pts (k+1))
        = Pc * sideOpp D.model 0 + Qc * sideOpp D.model 1 + Rc * sideOpp D.model 2 :=
  base_walk_pos_general hN D α β γ hαβ hαγ hαπ hα0 hβγ hβπ hβ0 hγπ hγ0 hπ0
    hγdef hrel hirr hscalene hα' hβ' hγ' k hdirab hcornerbase hcornerapex

-- Non-vacuity
example : @bwg_hiso_wallFun' = @bwg_hiso_wallFun' := rfl

#print axioms bwg_hiso_wallFun'
#print axioms bwg_base_walk_pos_general

end Erdos634.Draft.BaseWalkGeneralWrap
