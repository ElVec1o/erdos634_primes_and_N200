import Erdos634.BaseDecomposition

/-!
# Base walk (a,b,c)-word classification: wrapper

Key result:
- `bd_base_decomposition`: given a congruent dissection with (e,f)-model and base-β corner,
  the walk word along the base has one of two forms: (0,e,2e) or (f,e,e).

No `sorry`; standard axioms only.
-/

namespace Erdos634.Draft.BaseDecompositionWrap

open Erdos634.Geometry Erdos634.Geometry.Dissection Erdos634.SideWall
    Erdos634.TilePlacement Erdos634.SideWalk

theorem bd_base_decomposition {N : ℕ} (hN : 0 < N) (D : CongruentDissection N)
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
      (D.target.pts (k + 1 + 2)) = 3 * α)
    (e0 f0 : ℕ) (he0 : 1 ≤ e0) (hef0 : e0 < f0) (hco : Nat.Coprime e0 f0)
    (hsep : 2 * e0 * f0 + e0 * e0 < f0 * f0)
    (hA : sideOpp D.model 0 = ((e0 * f0 : ℕ) : ℝ))
    (hB : sideOpp D.model 1 = ((f0 * f0 - e0 * e0 : ℕ) : ℝ))
    (hC : sideOpp D.model 2 = ((f0 * f0 : ℕ) : ℝ))
    (hLen : dist (D.target.pts k) (D.target.pts (k+1))
      = ((e0 * (3 * (f0 * f0) - e0 * e0) : ℕ) : ℝ)) :
    ∃ x y z : ℕ, (x = 0 ∧ y = e0 ∧ z = 2 * e0) ∨ (x = f0 ∧ y = e0 ∧ z = e0) :=
  base_decomposition_general hN D α β γ hαβ hαγ hαπ hα0 hβγ hβπ hβ0 hγπ hγ0 hπ0
    hγdef hrel hirr hscalene hα' hβ' hγ' k hdirab hcornerbase hcornerapex
    e0 f0 he0 hef0 hco hsep hA hB hC hLen

#print axioms bd_base_decomposition

end Erdos634.Draft.BaseDecompositionWrap
