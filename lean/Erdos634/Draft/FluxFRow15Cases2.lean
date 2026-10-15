-- Draft/FluxFRow15Cases2.lean: cases 3 and 6 of the ten-case split for the target `(2α, α, 2β)`.
-- Continuation of `Draft/FluxFRow15.lean` (case 10, `k_s_ne_k_v`) and `Draft/FluxFRow15Cases.lean`
-- (cases 1, 2, 4, 5).
--
-- Case 3 (deg 3). The quartic `r⁴+r³−4r²−2r+5` (the numerator of the quartic-in-`r` formula for `n_a`)
-- is positive for every real `r`, by the exact identity
--   r⁴ + r³ − 4r² − 2r + 5 = (r² + r/2 − 11/5)² + (3/20)(r + 2/3)² + 7/75,
-- whose right side is a sum of squares plus a positive constant; `ring` checks the identity. This gives
-- the global root-freeness needed, with no interval restriction and no Sturm sequence. As in
-- `row15_deg4_impossible`, the identification of the quartic's numerator with the actual word
-- coefficient `n_a` (through the coordinates of `Y` in `{1,s,s²,s³}` and the rational-root reduction of
-- the degree-3 case) is taken as a hypothesis.
--
-- Case 6 (deg 2, P ≥ 0, −1 < v ≤ −s). Here `v² ≥ s²`, so `g(v) ≤ g(s)`; also `Y(s) ≥ Y(v) > 0`, and the
-- equality case must be excluded. `Y(s) = Y(v)` means `h(s) = h(v)` (same denominator, both nonzero),
-- i.e. `(v−s)(1+v+s) = 0` (a `ring`-checked identity). Since `v ≤ −s < 0 < s` forces `v ≠ s`, this gives
-- `1 + v + s = 0`, i.e. `v = −1 − s`; but `s > 0` (hypothesis `hs0`) makes `v < −1`, contradicting
-- `hv1 : −1 < v`. So only the strict case `Y(v) < Y(s)` survives, closed as in case 5.
--
-- Cases 7, 8, 9 are treated in `Draft/FluxFRow15Calculus.lean`; they rest on the strict monotonicity of
-- `F` on `(−1,1)`, a derivative-sign fact.
import Mathlib.Tactic
import Erdos634.Draft.FluxFRow15
import Erdos634.Draft.FluxFRow15Cases

open scoped Classical

namespace Erdos634.Row15Cases2

open Erdos634.Row15 (g)
open Erdos634.Row15Cases (h Y)

/-! ### Leaf 3 (of the ten) — degree 3: the quartic `r⁴+r³−4r²−2r+5` has no real root. -/

/-- **The exact sum-of-squares identity**, found by centering two squares on a numerically located
near-minimizer and then verifying the polynomial identity symbolically (see file header) — the
identity itself, checked here by `ring`, is what carries the proof; the numerics only located it. -/
theorem quartic_sos (r : ℝ) :
    r ^ 4 + r ^ 3 - 4 * r ^ 2 - 2 * r + 5 =
      (r ^ 2 + r / 2 - 11 / 5) ^ 2 + (3 / 20) * (r + 2 / 3) ^ 2 + 7 / 75 := by
  ring

/-- **The quartic is positive for every real `r`** (global, no interval restriction — exactly what
leaf 3 needs and what the file header of `FluxFRow15Cases.lean` doubted was available by
elementary means). -/
theorem quartic_pos (r : ℝ) : 0 < r ^ 4 + r ^ 3 - 4 * r ^ 2 - 2 * r + 5 := by
  rw [quartic_sos]
  have h1 : (0:ℝ) ≤ (r ^ 2 + r / 2 - 11 / 5) ^ 2 := sq_nonneg _
  have h2 : (0:ℝ) ≤ (3 / 20) * (r + 2 / 3) ^ 2 := by positivity
  linarith

/-- **Leaf 3 (deg 3) closed**: if `M ≥ 1`, `r ≠ 1`, `r ≠ −2`, and the s-coordinate `n_a` of `Y`'s
word equals `−M·(r⁴+r³−4r²−2r+5)/((r−1)²(r+2)²)` exactly as §5 computes for the degree-3 case,
then `n_a` cannot be a non-negative integer (`F3`). Same shape as leaf 1
(`row15_deg4_impossible`, `FluxFRow15Cases.lean`): the word-coefficient identification is a
hypothesis (`hna`), the arithmetic contradiction is what is proved. -/
theorem row15_deg3_impossible (M : ℤ) (r : ℝ) (hM : 1 ≤ M) (hr1 : r ≠ 1) (hr2 : r ≠ -2)
    (na : ℤ) (hna_nonneg : 0 ≤ na)
    (hna : (na : ℝ) = -(M : ℝ) * (r ^ 4 + r ^ 3 - 4 * r ^ 2 - 2 * r + 5) /
      ((r - 1) ^ 2 * (r + 2) ^ 2)) : False := by
  have hMr : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hquart : 0 < r ^ 4 + r ^ 3 - 4 * r ^ 2 - 2 * r + 5 := quartic_pos r
  have hr1' : r - 1 ≠ 0 := sub_ne_zero.mpr hr1
  have hr2' : r + 2 ≠ 0 := by intro hcon; apply hr2; linarith
  have h1sq : (0:ℝ) < (r - 1) ^ 2 := by
    rcases lt_or_gt_of_ne hr1' with hlt1 | hlt1
    · nlinarith
    · nlinarith
  have h2sq : (0:ℝ) < (r + 2) ^ 2 := by
    rcases lt_or_gt_of_ne hr2' with hlt2 | hlt2
    · nlinarith
    · nlinarith
  have hden : (0:ℝ) < (r - 1) ^ 2 * (r + 2) ^ 2 := mul_pos h1sq h2sq
  have hnum : (0:ℝ) < (M : ℝ) * (r ^ 4 + r ^ 3 - 4 * r ^ 2 - 2 * r + 5) :=
    mul_pos (by linarith) hquart
  have hlt : (na : ℝ) < 0 := by
    rw [hna]
    exact div_neg_of_neg_of_pos (by linarith) hden
  have hge : (0 : ℝ) ≤ (na : ℝ) := by exact_mod_cast hna_nonneg
  linarith

/-! ### Leaf 6 (of the ten) — degree 2, `P ≥ 0`, `−1 < v ≤ −s`. -/

theorem g_v_le_g_s_leaf6 (s v : ℝ) (hs0 : 0 < s) (hs1 : s < 1) (hv1 : -1 < v) (hv2 : v ≤ -s) :
    g v ≤ g s := by
  unfold g
  have hvs : s ≤ -v := by linarith
  have hv0 : 0 ≤ -v := by linarith
  have hsqle : s ^ 2 ≤ v ^ 2 := by nlinarith [mul_le_mul hvs hvs hs0.le hv0]
  have hsum_lt2 : s ^ 2 + v ^ 2 < 2 := by nlinarith
  -- g(v) - g(s) = (v²-s²) * ((v²+s²) - 5), and (v²+s²) - 5 < -3 < 0, v²-s² ≥ 0
  nlinarith [mul_nonneg (sub_nonneg.mpr hsqle) (by linarith : (0:ℝ) ≤ 5 - (v ^ 2 + s ^ 2))]

theorem h_v_pos_leaf6 (v : ℝ) (hv1 : -1 < v) (hv2 : v < 1) : 0 < h v := by
  unfold Erdos634.Row15Cases.h; nlinarith

theorem h_s_pos_leaf6 (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) : 0 < h s := by
  unfold Erdos634.Row15Cases.h; nlinarith

/-- **The equality case is impossible**: if `Y s = Y v` (with `s ∈ (0,1)`, `v ∈ (−1,−s]`), then
`False`. This is the sub-argument leaf 6 needs beyond leaves 4/5's pattern (§5: "equality would
force `v = −s` and `1+s+v = 0`, which is impossible") — resolved directly here via `h s = h v`. -/
theorem row15_leaf6_no_equality (s v : ℝ) (hs0 : 0 < s) (hs1 : s < 1)
    (hv1 : -1 < v) (hv2 : v ≤ -s) (hYeq : Y s = Y v) : False := by
  have hs2 : v < 1 := by linarith
  have hhs : 0 < h s := h_s_pos_leaf6 s hs0 hs1
  have hhv : 0 < h v := h_v_pos_leaf6 v hv1 hs2
  have hYeq' : (1:ℝ) / h s = 1 / h v := by
    unfold Erdos634.Row15Cases.Y at hYeq; exact hYeq
  have hheq : h s = h v := by
    have hcross := (div_eq_div_iff hhs.ne' hhv.ne').mp hYeq'
    linarith [hcross]
  have hfact : (v - s) * (1 + v + s) = 0 := by
    have hid : (v - s) * (1 + v + s) = h s - h v := by unfold Erdos634.Row15Cases.h; ring
    rw [hid, hheq]; ring
  have hvs : v - s ≠ 0 := by
    intro hc
    have : v = s := by linarith
    rw [this] at hv2
    linarith
  have hsum : 1 + v + s = 0 := by
    rcases mul_eq_zero.mp hfact with h1 | h1
    · exact absurd h1 hvs
    · exact h1
  linarith

/-- **Leaf 6 (deg 2, `P ≥ 0`, `−1 < v ≤ −s`) closed** (its arithmetic core; the bridge `Y v ≤ Y s`
is a hypothesis, as in leaves 4/5, see `FluxFRow15Cases.lean`'s header): if `s ∈ (0,1)`,
`v ∈ (−1,−s]`, `Y v ≤ Y s`, and `F(s) = F(v)` in the `g·Y²` form, then `False`. -/
theorem row15_Pge0_v_in_neg1_negs (s v : ℝ) (hs0 : 0 < s) (hs1 : s < 1)
    (hv1 : -1 < v) (hv2 : v ≤ -s) (hYle : Y v ≤ Y s)
    (hEq : g s * Y s ^ 2 = g v * Y v ^ 2) : False := by
  have hs2 : v < 1 := by linarith
  have hYv0 : 0 < Y v := by
    unfold Erdos634.Row15Cases.Y; exact div_pos one_pos (h_v_pos_leaf6 v hv1 hs2)
  have hYs0 : 0 < Y s := by
    unfold Erdos634.Row15Cases.Y; exact div_pos one_pos (h_s_pos_leaf6 s hs0 hs1)
  have hg : g v ≤ g s := g_v_le_g_s_leaf6 s v hs0 hs1 hv1 hv2
  have hgs2 : g s > 2 := Erdos634.Row15Cases.g_s_gt_two s hs0 hs1
  rcases hYle.lt_or_eq with hlt | heq
  · -- strict case: same chain as leaves 4/5
    have hsq : Y v ^ 2 < Y s ^ 2 := by nlinarith
    have hchain1 : g s * Y v ^ 2 < g s * Y s ^ 2 := by nlinarith
    have hchain2 : g v * Y v ^ 2 ≤ g s * Y v ^ 2 := by nlinarith [mul_nonneg hYv0.le hYv0.le]
    nlinarith
  · -- equality case: impossible outright
    exact row15_leaf6_no_equality s v hs0 hs1 hv1 hv2 heq.symm

end Erdos634.Row15Cases2

#print axioms Erdos634.Row15Cases2.quartic_sos
#print axioms Erdos634.Row15Cases2.quartic_pos
#print axioms Erdos634.Row15Cases2.row15_deg3_impossible
#print axioms Erdos634.Row15Cases2.g_v_le_g_s_leaf6
#print axioms Erdos634.Row15Cases2.h_v_pos_leaf6
#print axioms Erdos634.Row15Cases2.h_s_pos_leaf6
#print axioms Erdos634.Row15Cases2.row15_leaf6_no_equality
#print axioms Erdos634.Row15Cases2.row15_Pge0_v_in_neg1_negs
