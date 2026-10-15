-- Draft/FluxFRow15Cases.lean: cases 1, 2, 4, 5 of the ten-case split for the target `(2α, α, 2β)`.
-- Continuation of `Draft/FluxFRow15.lean`, which closes case 10 (`k_s_ne_k_v`).
--
-- The ten cases, with the theorem closing each:
--   1. deg 4                                  `row15_deg4_impossible`
--   2. q = 1                                  `row15_q1_no_root`
--   3. deg 3                                  `Draft/FluxFRow15Cases2.lean`
--   4. deg 2, P ≥ 0, v < −2                   `row15_Pge0_v_lt_neg2`
--   5. deg 2, P ≥ 0, −2 < v < −1              `row15_Pge0_v_in_neg2_neg1`
--   6. deg 2, P ≥ 0, −1 < v ≤ −s              `Draft/FluxFRow15Cases2.lean`
--   7. deg 2, P < 0, v ∉ (−1, 1)              `Draft/FluxFRow15Calculus.lean`
--   8. deg 2, P < 0, v ∈ [√2, √3]             `Draft/FluxFRow15Calculus.lean`
--   9. deg 2, P < 0, v ≥ 1.7                  `Draft/FluxFRow15Calculus.lean`
--  10. deg 2, P < 0, v ∈ (1, √2)              `k_s_ne_k_v` in `Draft/FluxFRow15.lean`
--
-- Meaning of "closed". Each theorem closes the arithmetic core of its case, the sign or inequality
-- computation, and takes the geometric fact ("the words force `X(s) ≥ X(v)`" or `Y(s) ≥ Y(v)`, from the
-- conjugate principle applied to a real side word) as a hypothesis, as `FluxFRow15.k_s_ne_k_v` does for
-- case 10. Deriving such a comparison from an actual word equation on a real `CongruentDissection` side,
-- as `FluxFRow14.row14_word_to_std_form` derives its `r·s + c0 = 0` form, needs the conjugate-principle
-- machinery (word coefficients read through the two embeddings of ℚ(s)); for the target here it is
-- developed in `Draft/FluxFRow15Conj.lean`.
--
-- Remarks on the cases not treated in this file.
--   * Case 3 (deg 3) needs that a quartic in `r` has no real root, a global statement on all of ℝ,
--     harder in shape than the interval bounds used here (bounded `x` allows `x⁴ ≤ Bx²`-type bounds;
--     unbounded `x` does not).
--   * Cases 6 to 9 each mix an arithmetic sign or monotonicity fact with the conjugate-principle bridge.
--     Case 6 also needs an equality-case exclusion (equality would force `v = −s` and `1+s+v = 0`, which
--     is impossible); cases 7 to 9 need a global monotonicity fact for `F` on `(−1,1)` (the sign of the
--     numerator of `F′`).
import Mathlib.Tactic
import Erdos634.Draft.FluxFRow15

open scoped Classical

namespace Erdos634.Row15Cases

open Erdos634.Row15 (g)

/-! ### Case 1 (of ten): degree 4. `n_a = −M(q+1)/2 < 0` is impossible against `n_a ≥ 0` (`F3`).

The word of `Y = M/h` then has `s`-coordinate `n_a = −M(q+1)/2 < 0`. The arithmetic core is the sign
computation; the identification of that coefficient with the actual word coefficient (via linear
independence over ℚ of the degree-4 basis `{1,s,s²,s³}`) is taken as the hypothesis `hna`, in the same way
as `FluxFRow14.row14_word_to_std_form` packages a stated word-coefficient identity as a hypothesis. -/

/-- **Leaf 1 (deg 4) closed**: if `M ≥ 1`, `q > 0`, and the s-coordinate `n_a` of `Y`'s word equals
`−M(q+1)/2` exactly as §5 computes (review 2a repair 1), then `n_a` cannot be a non-negative integer
(`F3`). -/
theorem row15_deg4_impossible (M : ℤ) (q : ℝ) (hM : 1 ≤ M) (hq : 0 < q)
    (na : ℤ) (hna_nonneg : 0 ≤ na) (hna : (na : ℝ) = -(M : ℝ) * (q + 1) / 2) : False := by
  have hMr : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hlt : (na : ℝ) < 0 := by nlinarith
  have hge : (0 : ℝ) ≤ (na : ℝ) := by exact_mod_cast hna_nonneg
  linarith

/-! ### Leaf 2 (of the ten) — `q = 1`: the cubic `2(s³+s²−2s−1)` has no root in `(0,1)`.

§5: "The polynomial is `2(s³+s²−2s−1)`, whose roots are `2cos(2πk/7)`. None lies in `(0,1)`." The
root-identification via `2cos(2πk/7)` is not needed for the row-15 argument itself — only that the
cubic has no root in the open unit interval, which is what actually excludes `s ∈ (0,1)` there.
Proved directly by bounding, without invoking the trigonometric root description at all. -/

/-- **Leaf 2 (`q = 1`) closed**: `2s³ + 2s² − 4s − 2 ≠ 0` for every `s ∈ (0,1)`. -/
theorem row15_q1_no_root (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) :
    2 * s ^ 3 + 2 * s ^ 2 - 4 * s - 2 ≠ 0 := by
  intro h
  nlinarith [sq_nonneg s, sq_nonneg (s - 1), sq_nonneg (1 - s), mul_pos hs0 hs0,
    mul_pos hs0 (sub_pos.mpr hs1), mul_nonneg hs0.le (sub_pos.mpr hs1).le,
    mul_nonneg (mul_pos hs0 hs0).le (sub_pos.mpr hs1).le]

/-! ### Leaves 4–5 (of the ten) — degree 2, `P ≥ 0`, the first two `v`-intervals.

Common definitions, exactly as §5 sets them up: `h(x) = (1−x)(2+x)`, `X(x) = (2−x²)/h(x)` (opposite
`2α`), `Y(x) = 1/h(x)` (opposite `α`), `ρ(x) = (3−x²)/(2−x²)`, and `g` (imported from
`FluxFRow15.lean`, `= (2−x²)(3−x²)`). Two equivalent forms of the tiling function are used, matching
the two the file itself uses across the sub-cases: `F = X²·ρ` (leaf 4's own working) and `F = g·Y²`
(leaf 5's own working); §0's sine table already records `F = g·Y² = X²·ρ` as the same function. -/

noncomputable def h (x : ℝ) : ℝ := (1 - x) * (2 + x)
noncomputable def X (x : ℝ) : ℝ := (2 - x ^ 2) / h x
noncomputable def Y (x : ℝ) : ℝ := 1 / h x
noncomputable def rho (x : ℝ) : ℝ := (3 - x ^ 2) / (2 - x ^ 2)

theorem rho_s_gt_three_half (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) : rho s > 3 / 2 := by
  have h2s : (0 : ℝ) < 2 - s ^ 2 := by nlinarith
  have hs2 : (0 : ℝ) < s ^ 2 := pow_pos hs0 2
  have hden : (0 : ℝ) < 2 * (2 - s ^ 2) := by nlinarith
  have hkey : rho s - 3 / 2 = s ^ 2 / (2 * (2 - s ^ 2)) := by unfold rho; field_simp; ring
  have hpos : (0 : ℝ) < s ^ 2 / (2 * (2 - s ^ 2)) := div_pos hs2 hden
  have := hkey ▸ hpos
  linarith

theorem rho_v_lt_one (v : ℝ) (hv : v < -2) : rho v < 1 := by
  have h2v : 2 - v ^ 2 < 0 := by nlinarith
  have hne : (2 : ℝ) - v ^ 2 ≠ 0 := ne_of_lt h2v
  have hkey : rho v - 1 = 1 / (2 - v ^ 2) := by unfold rho; field_simp; ring
  have hneg : (1 : ℝ) / (2 - v ^ 2) < 0 := div_neg_of_pos_of_neg one_pos h2v
  have := hkey ▸ hneg
  linarith

theorem X_v_pos_lt_neg2 (v : ℝ) (hv : v < -2) : 0 < X v := by
  have hnum : 2 - v ^ 2 < 0 := by nlinarith
  have hden : h v < 0 := by unfold h; nlinarith
  unfold X
  exact div_pos_of_neg_of_neg hnum hden

theorem X_s_pos (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) : 0 < X s := by
  have hnum : (0 : ℝ) < 2 - s ^ 2 := by nlinarith
  have hden : (0 : ℝ) < h s := by unfold h; nlinarith
  unfold X
  exact div_pos hnum hden

/-- **Leaf 4 (deg 2, `P ≥ 0`, `v < −2`) closed** (its arithmetic core; the bridge `X v ≤ X s` is a
hypothesis, see the file header): if `s ∈ (0,1)`, `v < −2`, `X v ≤ X s`, and `F(s) = F(v)` in the
`X²ρ` form, then `False`. -/
theorem row15_Pge0_v_lt_neg2 (s v : ℝ) (hs0 : 0 < s) (hs1 : s < 1) (hv : v < -2)
    (hXle : X v ≤ X s) (hEq : X s ^ 2 * rho s = X v ^ 2 * rho v) : False := by
  have hXv0 : 0 < X v := X_v_pos_lt_neg2 v hv
  have hXs0 : 0 < X s := X_s_pos s hs0 hs1
  have hrs : rho s > 3 / 2 := rho_s_gt_three_half s hs0 hs1
  have hrv : rho v < 1 := rho_v_lt_one v hv
  have hsq : X v ^ 2 ≤ X s ^ 2 := by nlinarith
  have hchain1 : X v ^ 2 * rho s ≤ X s ^ 2 * rho s := by nlinarith
  have hchain2 : X v ^ 2 * rho v < X v ^ 2 * rho s := by nlinarith [sq_nonneg (X v), mul_pos hXv0 hXv0]
  nlinarith

theorem g_v_lt_two (v : ℝ) (hv1 : -2 < v) (hv2 : v < -1) : g v < 2 := by
  unfold g
  have h1 : v ^ 2 - 1 > 0 := by nlinarith
  have h2 : v ^ 2 - 4 < 0 := by nlinarith
  have hexpand : (2 - v ^ 2) * (3 - v ^ 2) - 2 = (v ^ 2 - 1) * (v ^ 2 - 4) := by ring
  nlinarith [mul_neg_of_pos_of_neg h1 h2, hexpand]

theorem g_s_gt_two (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) : g s > 2 := by
  unfold g
  have h1 : s ^ 2 - 1 < 0 := by nlinarith
  have h2 : s ^ 2 - 4 < 0 := by nlinarith
  have hexpand : (2 - s ^ 2) * (3 - s ^ 2) - 2 = (s ^ 2 - 1) * (s ^ 2 - 4) := by ring
  nlinarith [mul_pos_of_neg_of_neg h1 h2, hexpand]

theorem Y_v_pos_mid (v : ℝ) (hv1 : -2 < v) (hv2 : v < -1) : 0 < Y v := by
  have hden : (0 : ℝ) < h v := by unfold h; nlinarith
  unfold Y
  exact div_pos one_pos hden

theorem Y_s_pos (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) : 0 < Y s := by
  have hden : (0 : ℝ) < h s := by unfold h; nlinarith
  unfold Y
  exact div_pos one_pos hden

/-- **Leaf 5 (deg 2, `P ≥ 0`, `−2 < v < −1`) closed** (its arithmetic core; the bridge `Y v ≤ Y s`
is a hypothesis, see the file header): if `s ∈ (0,1)`, `v ∈ (−2,−1)`, `Y v ≤ Y s`, and
`F(s) = F(v)` in the `g·Y²` form, then `False`. -/
theorem row15_Pge0_v_in_neg2_neg1 (s v : ℝ) (hs0 : 0 < s) (hs1 : s < 1)
    (hv1 : -2 < v) (hv2 : v < -1) (hYle : Y v ≤ Y s)
    (hEq : g s * Y s ^ 2 = g v * Y v ^ 2) : False := by
  have hYv0 : 0 < Y v := Y_v_pos_mid v hv1 hv2
  have hYs0 : 0 < Y s := Y_s_pos s hs0 hs1
  have hgs : g s > 2 := g_s_gt_two s hs0 hs1
  have hgv : g v < 2 := g_v_lt_two v hv1 hv2
  have hsq : Y v ^ 2 ≤ Y s ^ 2 := by nlinarith
  have hchain1 : g s * Y v ^ 2 ≤ g s * Y s ^ 2 := by nlinarith
  have hchain2 : g v * Y v ^ 2 < g s * Y v ^ 2 := by nlinarith [mul_pos hYv0 hYv0]
  nlinarith

end Erdos634.Row15Cases

#print axioms Erdos634.Row15Cases.row15_deg4_impossible
#print axioms Erdos634.Row15Cases.row15_q1_no_root
#print axioms Erdos634.Row15Cases.rho_s_gt_three_half
#print axioms Erdos634.Row15Cases.rho_v_lt_one
#print axioms Erdos634.Row15Cases.X_v_pos_lt_neg2
#print axioms Erdos634.Row15Cases.X_s_pos
#print axioms Erdos634.Row15Cases.row15_Pge0_v_lt_neg2
#print axioms Erdos634.Row15Cases.g_v_lt_two
#print axioms Erdos634.Row15Cases.g_s_gt_two
#print axioms Erdos634.Row15Cases.Y_v_pos_mid
#print axioms Erdos634.Row15Cases.Y_s_pos
#print axioms Erdos634.Row15Cases.row15_Pge0_v_in_neg2_neg1
