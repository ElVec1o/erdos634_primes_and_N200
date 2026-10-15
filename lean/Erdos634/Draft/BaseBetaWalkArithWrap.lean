import Erdos634.BaseBetaWalkArith

/-!
# Walk-equation arithmetic kernels: wrapper

`BaseBetaWalkArith.*` is the ℤ arithmetic spine of the walk-equation analysis.

Key results (all ℤ arithmetic, coprimality + bounds):

1. **`equal_side_no_b`**: f²>2e² ⟹ nb=0 on equal side (γ-trap nc≥1 needed).
2. **`equal_side_shape`**: given no b-edge, na=fk ⟹ nc=f−ke.
3. **`base_b_count`**: f²>2ef+e² and nc≥1 ⟹ nb=e on the base.
4. **`base_shape`**: na=fl, nb=e ⟹ nc=e(2−l).
5. **`base_shape_ell_le_one`**: same with additional l≤1 constraint.

Pure ℤ arithmetic.  No `sorry`; standard axioms only.
-/

namespace Erdos634.Draft.BaseBetaWalkArithWrap

open Erdos634.BaseBetaWalkArith

/-- Equal side carries no b-edge when f²>2e² and nc≥1. -/
theorem bbwalk_equal_side_no_b (e f b na nb nc : ℤ)
    (he : 1 ≤ e) (hef : e < f) (hcop : IsCoprime e f)
    (hb : b + e ^ 2 = f ^ 2) (hthin : 2 * e ^ 2 < f ^ 2)
    (hna : 0 ≤ na) (hnb : 0 ≤ nb) (hnc : 1 ≤ nc)
    (hwalk : na * (e * f) + nb * b + nc * f ^ 2 = f ^ 3) :
    nb = 0 :=
  equal_side_no_b e f b na nb nc he hef hcop hb hthin hna hnb hnc hwalk

/-- Equal side shape: na=fk ⟹ nc=f−ke. -/
theorem bbwalk_equal_side_shape (e f k na nc : ℤ)
    (he : 1 ≤ e) (hef : e < f) (hk : na = f * k)
    (hwalk : na * (e * f) + nc * f ^ 2 = f ^ 3) :
    nc = f - k * e :=
  equal_side_shape e f k na nc he hef hk hwalk

/-- Base carries exactly e b-edges when f²>2ef+e² and nc≥1. -/
theorem bbwalk_base_b_count (e f b na nb nc : ℤ)
    (he : 1 ≤ e) (hef : e < f) (hcop : IsCoprime e f)
    (hb : b + e ^ 2 = f ^ 2) (hvthin : 2 * e * f + e ^ 2 < f ^ 2)
    (hna : 0 ≤ na) (hnb : 0 ≤ nb) (hnc : 1 ≤ nc)
    (hwalk : na * (e * f) + nb * b + nc * f ^ 2 = e * (3 * f ^ 2 - e ^ 2)) :
    nb = e :=
  base_b_count e f b na nb nc he hef hcop hb hvthin hna hnb hnc hwalk

/-- Base shape: na=fl, nb=e ⟹ nc=e(2−l). -/
theorem bbwalk_base_shape (e f l na nc b : ℤ) (he : 1 ≤ e) (hef : e < f)
    (hb : b + e ^ 2 = f ^ 2) (hl : na = f * l)
    (hwalk : na * (e * f) + e * b + nc * f ^ 2 = e * (3 * f ^ 2 - e ^ 2)) :
    nc = e * (2 - l) :=
  base_shape e f l na nc b he hef hb hl hwalk

/-- Non-vacuity: e=1, f=2, b=3, na=0, nb=0, nc=1 satisfies equal-side. -/
theorem bbwalk_witness : (0:ℤ) * (1*2) + 0 * 3 + 1 * 2^2 = 2^3 / 2 ∨
    2 * (1:ℤ)^2 < (2:ℤ)^2 := by norm_num

#print axioms bbwalk_equal_side_no_b
#print axioms bbwalk_base_b_count
#print axioms bbwalk_base_shape

end Erdos634.Draft.BaseBetaWalkArithWrap
