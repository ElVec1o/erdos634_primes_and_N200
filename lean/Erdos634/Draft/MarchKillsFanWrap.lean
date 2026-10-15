import Erdos634.MarchKillsFan

/-!
# MarchKillsFan — march fan angle lemmas: wrapper

Key results wrapped:
- `fans_agree`: γ - 2α = β
- `modelAlpha_pos`, `modelAlpha_lt_pi_div_three`, `modelAlpha_lt_modelBeta`
- `modelAlpha_irrational`: α irrational for f ≥ 2
- `beta_sub_alpha_not_cone`: β−α is not a corner sum
- `pi_point_no_fourth_alpha`: 4th α impossible at π-point
- `distinct_of_order`: α, β, γ, π all distinct

No sorry; standard axioms.
-/

namespace Erdos634.Draft.MarchKillsFanWrap

open Erdos634.MarchKillsFan Erdos634.Geometry Erdos634.BaseBetaTargetCoord

theorem mkf_fans_agree {α β γ : ℝ} (hγ : γ = 2 * α + β) : γ - (α + α) = β :=
  fans_agree hγ

theorem mkf_modelAlpha_pos {f : ℝ} (hf : 1 < f) : 0 < modelAlpha 1 f :=
  modelAlpha_pos hf

theorem mkf_modelAlpha_lt_pi_div_three {f : ℝ} (hf : 1 < f) :
    modelAlpha 1 f < Real.pi / 3 :=
  modelAlpha_lt_pi_div_three hf

theorem mkf_modelAlpha_lt_modelBeta {f : ℝ} (hf : 2 ≤ f) :
    modelAlpha 1 f < modelBeta 1 f :=
  modelAlpha_lt_modelBeta hf

theorem mkf_modelAlpha_irrational (f : ℕ) (hf : 2 ≤ f) :
    ¬ ∃ r : ℚ, modelAlpha 1 (f : ℝ) = (r : ℝ) * Real.pi :=
  modelAlpha_irrational f hf

theorem mkf_beta_sub_alpha_not_cone {α β : ℝ} (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (X Y : ℕ) :
    (X : ℝ) * α + (Y : ℝ) * β ≠ β - α :=
  beta_sub_alpha_not_cone hrel hirr X Y

theorem mkf_pi_point_no_fourth_alpha (na nb ng : ℕ) (hx : na + 2 * ng = 3)
    (hy : nb + ng = 2) : na ≤ 3 :=
  pi_point_no_fourth_alpha na nb ng hx hy

theorem mkf_distinct_of_order {α β γ : ℝ} (hα : 0 < α) (hαβ : α < β) (hγ : γ = 2 * α + β)
    (hrel : 3 * α + 2 * β = Real.pi) :
    α ≠ β ∧ α ≠ γ ∧ α ≠ Real.pi ∧ α ≠ 0 ∧ β ≠ γ ∧ β ≠ Real.pi ∧ β ≠ 0 ∧
    γ ≠ Real.pi ∧ γ ≠ 0 ∧ Real.pi ≠ 0 :=
  distinct_of_order hα hαβ hγ hrel

-- Non-vacuity: fans_agree at α=1,β=0,γ=2
example : (2 : ℝ) - (1 + 1) = 0 := mkf_fans_agree (α := 1) (β := 0) (γ := 2) (by ring)

#print axioms mkf_modelAlpha_pos
#print axioms mkf_modelAlpha_irrational

end Erdos634.Draft.MarchKillsFanWrap
