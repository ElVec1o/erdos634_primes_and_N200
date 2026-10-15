-- Draft/FluxFRow15.lean: on the target `(2α, α, 2β)`, an `N`-tiling (any `N`, reflections allowed, not
-- necessarily edge-to-edge) by the `3α + 2β = π` tile with `α ∉ ℚπ` has a rational tile, `s := a/c ∈ ℚ`.
--
-- The route is pure algebra over the field ℚ(s) (degree and conjugate case split); it does not use the
-- flux functional, `GridChar` or `fAlpha`/`fBeta`.
--
-- This file contains the factorization identity
--   `k − 4/3 = (x−1)(3x⁴+6x³−9x²−24x−10)/(3(2+x))`,
-- stated as `k_minus_four_thirds` and checked by `ring`, where `k = g·(1+x)/(2+x)` and
-- `g(x) = (2−x²)(3−x²)` (so `F = g·Y²`). Check at `x = 0`: `k(0) = 2·3·1/2 = 3`, so `k(0) − 4/3 = 5/3`,
-- and the right side is `(0−1)·(−10)/6 = 5/3`.
--
-- Closed, unconditionally: `k_minus_four_thirds` (valid for all `x ≠ −2`) and `quartic_neg_on_Icc`
-- (the quartic `3x⁴+6x³−9x²−24x−10` is `< 0` for every `x ∈ [0, 3/2]`, by the bounds `x⁴ ≤ (3/2)²x²` and
-- `x³ ≤ (3/2)x²` on `[0, 3/2]`, reducing to a single quadratic bound closed by `nlinarith`).
-- `k_gt_four_thirds_on_unit` and `k_lt_four_thirds_gt_one` combine these into the two half-inequalities
-- consumed by the case "deg 2, P < 0, v ∈ (1, √2)": `k(s) > 4/3` for `s ∈ (0,1)` and `k(v) < 4/3` for
-- `v ∈ (1, 3/2]` (this covers `v ∈ (1, √2)` since `√2 < 3/2`).
--
-- Scope. Only this one case of the case split is treated here, and only its arithmetic core (the signs of
-- `k − 4/3`). The identification of `k(v) ≥ k(s)` from "Y needs `(v−1)²(v+1)(v+2) ≥ (1−s)²(1+s)(2+s)`"
-- and `F(s) = F(v)` is not formalized in this file; the other cases are treated in
-- `FluxFRow15Cases.lean`, `FluxFRow15Cases2.lean` and `FluxFRow15Calculus.lean`. There is no
-- `CongruentDissection`-level statement of the result in this file.
--
-- Non-vacuity. `k_minus_four_thirds` holds for every real `x ≠ −2` (for instance `x = 0`), and
-- `quartic_neg_on_Icc` has the hypothesis `x ∈ [0, 3/2]` (for instance `x = 1`, where `k(1) = 4/3`).
-- The certified tiling `Tiling77` (`s = 1/2`, `M = 5`) realizes the rational branch only (`NotRat s` is
-- false there), so none of the irrational-branch lemmas applies to it; an irrational branch has no real
-- tiling to exercise it.
import Mathlib.Tactic

open scoped Classical

namespace Erdos634.Row15

/-- `g(x) = (2 − x²)(3 − x²)`, the row-15 tiling-function factor (§0's sine table /
`F = g·Y²`, §5's opening line). -/
noncomputable def g (x : ℝ) : ℝ := (2 - x ^ 2) * (3 - x ^ 2)

/-- `k(x) = g(x)·(1 + x)/(2 + x)`, exactly as §5 defines it ("k(v) ≥ k(s), where
`k = g·(1+x)/(2+x)`"). -/
noncomputable def k (x : ℝ) : ℝ := g x * (1 + x) / (2 + x)

/-- **The factorization identity**:
`k(x) − 4/3 = (x−1)(3x⁴+6x³−9x²−24x−10) / (3(2+x))` for every `x ≠ −2`.
Machine-checked before anything is built on it. -/
theorem k_minus_four_thirds (x : ℝ) (hx : x ≠ -2) :
    k x - 4 / 3 = (x - 1) * (3 * x ^ 4 + 6 * x ^ 3 - 9 * x ^ 2 - 24 * x - 10) / (3 * (2 + x)) := by
  unfold k g
  have h2 : (2 : ℝ) + x ≠ 0 := by intro h; apply hx; linarith
  field_simp
  ring

/-- **The quartic factor is negative on `[0, 3/2]`** (review 2a's parenthetical, "whose quartic
factor is negative on [0, 3/2]"). Proved by the same bounding argument the repair implicitly uses:
on `[0, 3/2]`, `x⁴ ≤ (3/2)²x²` and `x³ ≤ (3/2)x²`, so the quartic is `≤ (27/4)x² − 24x − 10`, a
quadratic that is itself `≤ −10 < 0` on `[0, 3/2]` (it is decreasing there). -/
theorem quartic_neg_on_Icc (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 3 / 2) :
    3 * x ^ 4 + 6 * x ^ 3 - 9 * x ^ 2 - 24 * x - 10 < 0 := by
  nlinarith [sq_nonneg x, sq_nonneg (x - 3/2), mul_nonneg hx0 hx0,
    mul_nonneg (mul_nonneg hx0 hx0) hx0, mul_nonneg (mul_nonneg hx0 hx0) (mul_nonneg hx0 hx0),
    mul_nonneg hx0 (sub_nonneg.mpr hx1), mul_nonneg (mul_nonneg hx0 hx0) (sub_nonneg.mpr hx1)]

/-- **`k(s) > 4/3` for `s ∈ (0, 1)`**: the half of §5's "v ∈ (1, √2)" leaf applied at `s`. Since
`s ∈ (0,1) ⊂ [0, 3/2]`, `s − 1 < 0` and the quartic factor is negative, so their product is
positive; `3(2+s) > 0`; hence `k(s) − 4/3 > 0`. -/
theorem k_gt_four_thirds_on_unit (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) : k s > 4 / 3 := by
  have hs2 : s ≠ -2 := by linarith
  have hid := k_minus_four_thirds s hs2
  have hq : 3 * s ^ 4 + 6 * s ^ 3 - 9 * s ^ 2 - 24 * s - 10 < 0 :=
    quartic_neg_on_Icc s hs0.le (by linarith)
  have hnum : (s - 1) * (3 * s ^ 4 + 6 * s ^ 3 - 9 * s ^ 2 - 24 * s - 10) > 0 :=
    mul_pos_of_neg_of_neg (by linarith) hq
  have hden : (3:ℝ) * (2 + s) > 0 := by linarith
  have : (s - 1) * (3 * s ^ 4 + 6 * s ^ 3 - 9 * s ^ 2 - 24 * s - 10) / (3 * (2 + s)) > 0 :=
    div_pos hnum hden
  linarith [hid ▸ this]

/-- **`k(v) < 4/3` for `v ∈ (1, 3/2]`** (the review's `v ∈ (1, √2)` is contained here, since
`√2 < 3/2`): now `v − 1 > 0` and the quartic factor is still negative on `[1, 3/2] ⊆ [0, 3/2]`, so
the product is negative, giving `k(v) − 4/3 < 0`. -/
theorem k_lt_four_thirds_gt_one (v : ℝ) (hv1 : 1 < v) (hv2 : v ≤ 3 / 2) : k v < 4 / 3 := by
  have hv2' : v ≠ -2 := by linarith
  have hid := k_minus_four_thirds v hv2'
  have hq : 3 * v ^ 4 + 6 * v ^ 3 - 9 * v ^ 2 - 24 * v - 10 < 0 :=
    quartic_neg_on_Icc v (by linarith) hv2
  have hnum : (v - 1) * (3 * v ^ 4 + 6 * v ^ 3 - 9 * v ^ 2 - 24 * v - 10) < 0 :=
    mul_neg_of_pos_of_neg (by linarith) hq
  have hden : (3:ℝ) * (2 + v) > 0 := by linarith
  have : (v - 1) * (3 * v ^ 4 + 6 * v ^ 3 - 9 * v ^ 2 - 24 * v - 10) / (3 * (2 + v)) < 0 :=
    div_neg_of_neg_of_pos hnum hden
  linarith [hid ▸ this]

/-- **The contradiction §5's leaf needs**: for `s ∈ (0,1)` and `v ∈ (1, 3/2]`, `k(s) ≠ k(v)`
(in fact `k(v) < 4/3 < k(s)`). This is the arithmetic half of "k(v) < 4/3 < k(s). Contradiction" —
the geometric half (that the leaf's hypotheses FORCE `k(v) ≥ k(s)`, so this lemma applies to
derive `False`) is not built here; see the header's "NOT FORMALIZED" note. -/
theorem k_s_ne_k_v (s v : ℝ) (hs0 : 0 < s) (hs1 : s < 1) (hv1 : 1 < v) (hv2 : v ≤ 3 / 2) :
    k v < k s := by
  have h1 := k_gt_four_thirds_on_unit s hs0 hs1
  have h2 := k_lt_four_thirds_gt_one v hv1 hv2
  linarith

end Erdos634.Row15

#print axioms Erdos634.Row15.k_minus_four_thirds
#print axioms Erdos634.Row15.quartic_neg_on_Icc
#print axioms Erdos634.Row15.k_gt_four_thirds_on_unit
#print axioms Erdos634.Row15.k_lt_four_thirds_gt_one
#print axioms Erdos634.Row15.k_s_ne_k_v
