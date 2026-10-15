import Erdos634.SideWalk

namespace Erdos634.Draft.SideWalkWrap
open Erdos634.SideWalk Erdos634.Geometry Erdos634.Placement Erdos634.TilePlacement
open Erdos634.WallEndpoints Erdos634.BaseBetaWalkArith Erdos634.SideWall
open Erdos634.Geometry.Dissection

theorem wrap_base_shape_of_gammatrap {N : ℕ} (D : CongruentDissection N) (α β γ : ℝ)
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hαπ : α ≠ Real.pi) (hα0 : α ≠ 0)
    (hβγ : β ≠ γ) (hβπ : β ≠ Real.pi) (hβ0 : β ≠ 0)
    (hγπ : γ ≠ Real.pi) (hγ0 : γ ≠ 0) (hπ0 : Real.pi ≠ 0)
    (hγdef : γ = 2 * α + β) (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (hscalenef : ∀ m m' : Fin 3, m ≠ m' → sideOpp D.model m ≠ sideOpp D.model m')
    (hα' : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hβ' : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hγ' : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    (k : Fin 3) (dir : Plane →ₗ[ℝ] ℝ)
    (hker : ∀ v : Plane, (wallFun D.target k).linear v = 0 → dir v = 0 → v = 0)
    (hdirab : dir (D.target.pts k) ≤ dir (D.target.pts (k + 1)))
    (hthird : ∀ p ∈ Erdos634.BaseChain.wallList D.toDissection (wallFun D.target k) 0,
      wallFun D.target k ((D.tile p.1).pts (p.2 + 2)) < 0)
    (hcornerbase : cornerAngle (D.target.pts (k + 1)) (D.target.pts k)
      (D.target.pts (k + 2)) = β)
    (hcornerapex : cornerAngle (D.target.pts (k + 1 + 1)) (D.target.pts (k + 1))
      (D.target.pts (k + 1 + 2)) = 3 * α)
    (hiso : ∀ p q : Plane, (wallFun D.target k) p = 0 → (wallFun D.target k) q = 0 →
      dist p q = |dir p - dir q|)
    (hN : 0 < N) (e0 f0 b0 : ℤ) (he0 : 1 ≤ e0) (hef0 : e0 < f0) (hcop : IsCoprime e0 f0)
    (hb0 : b0 + e0 ^ 2 = f0 ^ 2) (hvthin : 2 * e0 * f0 + e0 ^ 2 < f0 ^ 2)
    (hA : sideOpp D.model 0 = ((e0 * f0 : ℤ) : ℝ))
    (hB : sideOpp D.model 1 = (b0 : ℝ))
    (hC : sideOpp D.model 2 = ((f0 ^ 2 : ℤ) : ℝ))
    (hLen : dist (D.target.pts k) (D.target.pts (k + 1))
      = ((e0 * (3 * f0 ^ 2 - e0 ^ 2) : ℤ) : ℝ)) :
    ∃ Pc l Rc : ℕ, (Pc : ℤ) = f0 * l ∧ (Rc : ℤ) = e0 * (2 - l) :=
  base_shape_of_gammatrap D α β γ hαβ hαγ hαπ hα0 hβγ hβπ hβ0 hγπ hγ0 hπ0
    hγdef hrel hirr hscalenef hα' hβ' hγ' k dir hker hdirab hthird hcornerbase hcornerapex
    hiso hN e0 f0 b0 he0 hef0 hcop hb0 hvthin hA hB hC hLen

example : True := trivial
#check @wrap_base_shape_of_gammatrap

end Erdos634.Draft.SideWalkWrap
