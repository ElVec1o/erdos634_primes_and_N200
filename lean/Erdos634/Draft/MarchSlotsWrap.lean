import Erdos634.MarchSlots

/-!
# MarchSlots — junction slot analysis: wrapper

Key results:
- `angleData_f3`: existence witness for `AngleData` at f=3
- `no_two_gamma`: no two γ-tiles at one interior base point
- `third_of_gamma_beta` / `third_of_gamma_alpha`: forced third tile in mixed configurations

No sorry; standard axioms.
-/

namespace Erdos634.Draft.MarchSlotsWrap

open Erdos634.MarchSlots Erdos634.Geometry Erdos634.TilePlacement
    Erdos634.BaseBetaTargetCoord Erdos634.MarchKillsFan Erdos634.MarchCoords Erdos634.CertCoord

theorem ms_angleData_f3 : ∃ α β γ : ℝ, AngleData α β γ :=
  angleData_f3

theorem ms_no_two_gamma {N : ℕ} (D : CongruentDissection N) {f α β γ : ℝ} (hf : 2 ≤ f)
    (htgt : D.target = baseBetaTarget 1 f one_pos (by linarith))
    (hM : ModelData D f α β γ) (hA : AngleData α β γ)
    {x₀ : ℝ} (hx0 : 0 < x₀) (hxL : x₀ < baseLen 1 f)
    {i j : Fin N} (hij : i ≠ j)
    (hi : (D.tile i).localAngle (mkPt x₀ 0) = γ)
    (hj : (D.tile j).localAngle (mkPt x₀ 0) = γ) : False :=
  no_two_gamma D hf htgt hM hA hx0 hxL hij hi hj

theorem ms_third_of_gamma_beta {N : ℕ} (D : CongruentDissection N) {f α β γ : ℝ} (hf : 2 ≤ f)
    (htgt : D.target = baseBetaTarget 1 f one_pos (by linarith))
    (hM : ModelData D f α β γ) (hA : AngleData α β γ)
    {x₀ : ℝ} (hx0 : 0 < x₀) (hxL : x₀ < baseLen 1 f)
    {i j : Fin N}
    (hi : (D.tile i).localAngle (mkPt x₀ 0) = γ)
    (hj : (D.tile j).localAngle (mkPt x₀ 0) = β) :
    ∃ l : Fin N, l ≠ i ∧ l ≠ j ∧ (D.tile l).localAngle (mkPt x₀ 0) = α ∧
      ∀ l', (D.tile l').localAngle (mkPt x₀ 0) = α → l' = l :=
  third_of_gamma_beta D hf htgt hM hA hx0 hxL hi hj

-- Non-vacuity witness
example : ∃ α β γ : ℝ, AngleData α β γ := ms_angleData_f3

#print axioms ms_angleData_f3
#print axioms ms_no_two_gamma
#print axioms ms_third_of_gamma_beta

end Erdos634.Draft.MarchSlotsWrap
