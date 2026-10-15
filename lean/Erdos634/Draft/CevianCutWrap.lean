import Erdos634.CevianCut

namespace Erdos634.Draft.CevianCutWrap

open Erdos634.CevianCut

theorem cc_base_sub_twice_foot (e f : ℤ) :
    baseLen e f - 2 * (e * f ^ 2) = e * sideB e f :=
  base_sub_twice_foot e f

theorem cc_four_AD_sq (e f : ℤ) :
    (baseLen e f - 2 * (e * f ^ 2)) ^ 2 + 4 * (legLen f) ^ 2 - (baseLen e f) ^ 2
      = 4 * (f * sideB e f) ^ 2 :=
  four_AD_sq e f

theorem cc_cut_triangle_is_scaled_tile (e f : ℤ) :
    e * f ^ 2 = f * sideA e f ∧
    f * sideB e f = f * sideB e f ∧
    legLen f = f * sideC f :=
  cut_triangle_is_scaled_tile e f

theorem cc_decomposition_count (f : ℤ) : f ^ 2 + (f ^ 2 - 1) + f ^ 2 = 3 * f ^ 2 - 1 :=
  decomposition_count f

example : cc_cut_triangle_is_scaled_tile 1 2 = cut_triangle_is_scaled_tile 1 2 := rfl

#print axioms cc_four_AD_sq

end Erdos634.Draft.CevianCutWrap
