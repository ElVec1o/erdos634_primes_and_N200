-- Draft/FDACaseG1125.lean — no sorry, no native_decide.
-- Arithmetic record: at N = 1125 every arithmetic helper hypothesis of the caseG_of_* family fails,
-- so the CaseGClosed leaf at 1125 is not dischargeable by those helpers. Also the N=71 area-ratio arithmetic.
import Erdos634.Draft.NSQLegs
import Erdos634.Draft.ChainComposite

namespace Erdos634.Draft.FDACaseG1125

open Erdos634.Geometry Erdos634.Draft.NSQLegs

theorem not_gammaArith_1125 : ¬ GammaArith 1125 := by
  intro h
  have := h 15 75 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  revert this; decide

theorem not_M1Div_1125 : ¬ M1Div 1125 := by
  intro h
  have := h 3 (by norm_num) (by norm_num)
  omega

theorem not_mod4_two_1125 : ¬ (1125 % 4 = 2) := by norm_num

theorem not_squarefree_1125 : ¬ Squarefree 1125 := by
  intro h
  have := h 3 ⟨125, by norm_num⟩
  exact absurd (isUnit_iff_eq_one.mp this) (by norm_num)

theorem not_any_caseG_helper_applies_1125 :
    ¬ GammaArith 1125 ∧ ¬ M1Div 1125 ∧ ¬ (1125 % 4 = 2) ∧ ¬ Squarefree 1125 :=
  ⟨not_gammaArith_1125, not_M1Div_1125, not_mod4_two_1125, not_squarefree_1125⟩

/-- N = 71 area ratio (Heron, squared): tile (10,21,25) has 16·area² = 4·10²·21²-(10²+21²-25²)², computed
as integers; target isosceles legs 125, base 142 has 16·area² = 142²(4·125²-142²). Ratio of areas is 71. -/
theorem tile_16A2 : 4 * 10^2 * 21^2 - (10^2 + 21^2 - 25^2 : ℤ)^2 = 16 * 10584 := by norm_num
theorem target_16A2 : (142:ℤ)^2 * (4 * 125^2 - 142^2) = 16 * 10584 * 71^2 := by norm_num
theorem area_ratio_71 : (142:ℤ)^2 * (4 * 125^2 - 142^2)
    = (71:ℤ)^2 * (4 * 10^2 * 21^2 - (10^2 + 21^2 - 25^2 : ℤ)^2) := by norm_num

end Erdos634.Draft.FDACaseG1125

#print axioms Erdos634.Draft.FDACaseG1125.not_any_caseG_helper_applies_1125
#print axioms Erdos634.Draft.FDACaseG1125.area_ratio_71
