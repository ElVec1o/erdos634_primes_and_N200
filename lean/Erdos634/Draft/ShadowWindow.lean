/-
Draft/ShadowWindow.lean -- the arithmetic clause of the shadow lemma at every member.

At scale one the base of the member `(e, f)` has length `e (3f² − e²)` and each corner shadow has length
`a cos β + c = e² (3f² − e²) / (2f²) + f²`, so the window left between the two shadows is
`W = e (3f² − e²)(f² − e) / f² − 2f²`.  Cleared of the denominator `f²`:

* `a_cos_beta`, `window_closed`: the two identities behind the closed form of `W`;
* `window_lt_b_e1` (`OrderForcing.shadow_footage_e1`): at `e = 1`, `W < b` for every `f ≥ 2`;
* `window_gt_b` : for `2 ≤ e < f`, `W > b`.

No sorry, no native_decide.
-/
import Erdos634.OrderForcing
import Mathlib.Tactic

namespace Erdos634.Draft.ShadowWindow

/-- at `e = 1` the window is shorter than `b = f² − 1` (form with the general expression at `e = 1`) -/
theorem window_lt_b_e1 (f : ℤ) (hf : 2 ≤ f) :
    1 * (3 * f ^ 2 - 1 ^ 2) * (f ^ 2 - 1) - 2 * f ^ 4 < (f ^ 2 - 1 ^ 2) * f ^ 2 := by
  have h := Erdos634.OrderForcing.shadow_footage_e1 f hf
  linarith

/-- for `2 ≤ e < f` the window is longer than `b = f² − e²` -/
theorem window_gt_b (e f : ℤ) (he : 2 ≤ e) (hef : e < f) :
    (f ^ 2 - e ^ 2) * f ^ 2 < e * (3 * f ^ 2 - e ^ 2) * (f ^ 2 - e) - 2 * f ^ 4 := by
  have hf2 : (e + 1) ^ 2 ≤ f ^ 2 := by nlinarith
  have hf0 : 0 < f ^ 2 := by nlinarith
  have h1 : 0 ≤ 3 * (e - 1) * f ^ 2 * (f ^ 2 - (e + 1) ^ 2) :=
    mul_nonneg (mul_nonneg (by linarith) hf0.le) (by linarith)
  have h2 : 0 < 2 * e ^ 3 + e ^ 2 - 3 * e - 3 := by
    nlinarith [mul_nonneg (show (0 : ℤ) ≤ e by linarith) (show (0 : ℤ) ≤ e ^ 2 - 4 by nlinarith)]
  have h3 : 0 < (2 * e ^ 3 + e ^ 2 - 3 * e - 3) * f ^ 2 := mul_pos h2 hf0
  have h4 : 0 ≤ e ^ 4 := by positivity
  nlinarith [h1, h3, h4]

/-- `a cos β` from the law of cosines for the tile `(a, b, c) = (ef, f² − e², f²)` (`β` opposite `b`):
`a (a² + c² − b²) / (2ac) = e² (3f² − e²) / (2f²)` -/
theorem a_cos_beta (e f : ℝ) (he : e ≠ 0) (hf : f ≠ 0) :
    (e * f) * (((e * f) ^ 2 + (f ^ 2) ^ 2 - (f ^ 2 - e ^ 2) ^ 2) / (2 * (e * f) * f ^ 2))
      = e ^ 2 * (3 * f ^ 2 - e ^ 2) / (2 * f ^ 2) := by
  field_simp
  ring

/-- the window between the two shadows, closed form: base `e (3f² − e²)` minus twice `a cos β + c` -/
theorem window_closed (e f : ℝ) (hf : f ≠ 0) :
    e * (3 * f ^ 2 - e ^ 2) - 2 * (e ^ 2 * (3 * f ^ 2 - e ^ 2) / (2 * f ^ 2) + f ^ 2)
      = e * (3 * f ^ 2 - e ^ 2) * (f ^ 2 - e) / f ^ 2 - 2 * f ^ 2 := by
  field_simp
  ring

/-- control at `(e, f) = (2, 3)`: `W f² = 160 > b f² = 45` -/
theorem control_2_3 : (2 : ℤ) * (3 * 3 ^ 2 - 2 ^ 2) * (3 ^ 2 - 2) - 2 * 3 ^ 4 = 160 ∧ ((3 : ℤ) ^ 2 - 2 ^ 2) * 3 ^ 2 = 45 := by
  constructor <;> norm_num

end Erdos634.Draft.ShadowWindow

#print axioms Erdos634.Draft.ShadowWindow.window_gt_b
