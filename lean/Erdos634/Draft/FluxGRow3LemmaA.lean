-- Draft/FluxGRow3LemmaA.lean — Lemma A's case split for a right tile. Imported directly by All.lean.
--
-- Setting: the tile has angles `α`, `β = π/2 − α` and `π/2`, with `α/π` irrational. The hypothesis is
-- that each of the three corners of the target has angle `A_i = p_i α + q_i β + r_i π/2` with
-- `(p_i, q_i, r_i) : ℕ × ℕ × ℕ` not all zero, each angle in `(0, π)`, and the three angles summing to `π`.
-- This hypothesis is an explicit assumption of every theorem in this file; the geometric fact that it
-- holds at the corners of a real dissection is in `FluxGRow3Step1`.
--
-- Contents:
--   * `lemmaA_sum`: the angle sum forces `Σ(p_i−q_i) = 0` and `Σ(q_i+r_i) = 2`.
--   * `corner_y_zero`, `corner_y_two_q_le`, `corner_y_two_lt`, `corner_y_one`: the facts used in both
--     patterns.
--   * `patternA_core`: the pattern (2,0,0), whose angles are `(2β, α, α)`.
--   * `patternB_core`: the pattern (1,1,0), with the sub-cases `p₃ = 1, 2` and the exclusion of `p₃ ≥ 3`.
--   * `lemmaA_case_split`: the six-way disjunction (three labelled instances of each pattern), whose
--     conclusion is: the target is similar to the tile, or has angles `(α, α, π−2α)`, or has angles
--     `(β, β, π−2β)`.
--
-- No Gaussian weight or flux appears in this file. `dy_eq_of_sum` clears a linear relation between `α`
-- and `π` by irrationality; it is a single equation without the `2π` periodicity term needed in
-- `Row3.grid_unique`, so it is proved separately.
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

open scoped Classical

namespace Erdos634.Geometry.Row3

open Real

/-! ## The corner-angle model (Lemma A step 2) -/

/-- **A corner's contributed angle**, `p·α + q·β + r·(π/2)` with `β = π/2 − α` substituted in
(Lemma A step 2: "corner i has angle `A_i = p_i α + q_i β + r_i π/2`... Substituting
`β = π/2 − α` gives `A_i = (p_i − q_i) α + (q_i + r_i) π/2`"). -/
noncomputable def cornerAngle (α : ℝ) (p q r : ℕ) : ℝ :=
  (p : ℝ) * α + (q : ℝ) * (Real.pi / 2 - α) + (r : ℝ) * (Real.pi / 2)

/-- The substituted form, `A = (p−q)·α + (q+r)·(π/2)`, matching step 2 literally. -/
theorem cornerAngle_eq (α : ℝ) (p q r : ℕ) :
    cornerAngle α p q r = (((p : ℤ) - (q : ℤ) : ℤ) : ℝ) * α + (((q + r : ℕ)) : ℝ) * (Real.pi / 2) := by
  unfold cornerAngle
  push_cast
  ring

/-! ## Steps 2-3: the angle-sum equation forces `Σ(p_i−q_i) = 0`, `Σ(q_i+r_i) = 2` -/

/-- **The arithmetic core of steps 2-3.** `D·α + Y·(π/2) = π` with `α ∉ ℚπ` forces `D = 0` and
`Y = 2`. This is "the angles sum to π and α ∉ ℚπ. Hence `Σ(p_i−q_i) = 0` and
`Σy_i = 2`", stripped of the corner-data packaging. Unlike `Row3.grid_unique` (FluxGRow3.lean), there
is no `2π`-periodicity term here (a triangle's angle sum is exactly `π`, not `π` mod `2π`), so this is
proved directly rather than by invoking `grid_unique`. -/
theorem dy_eq_of_sum {α : ℝ} (hα : Irrational (α / Real.pi)) (D : ℤ) (Y : ℕ)
    (heq : (D : ℝ) * α + (Y : ℝ) * (Real.pi / 2) = Real.pi) : D = 0 ∧ Y = 2 := by
  have hpi : (Real.pi : ℝ) ≠ 0 := Real.pi_ne_zero
  have hD0 : D = 0 := by
    by_contra hD
    have hDR : (2 * (D : ℝ)) ≠ 0 := by
      have h2 : (2 : ℝ) ≠ 0 := two_ne_zero
      have hd : (D : ℝ) ≠ 0 := by exact_mod_cast hD
      exact mul_ne_zero h2 hd
    apply hα
    refine ⟨(((2 : ℤ) - (Y : ℤ) : ℤ) : ℚ) / (((2 * D : ℤ)) : ℚ), ?_⟩
    rw [Rat.cast_div]
    push_cast
    rw [div_eq_div_iff hDR hpi]
    nlinarith [heq]
  refine ⟨hD0, ?_⟩
  subst hD0
  have h0 : (Y : ℝ) * (Real.pi / 2) = Real.pi := by simpa using heq
  have h2 : (Real.pi / 2 : ℝ) ≠ 0 := by positivity
  have hY : (Y : ℝ) = 2 := by
    have h1 : (Y : ℝ) * (Real.pi / 2) = 2 * (Real.pi / 2) := by rw [h0]; ring
    exact mul_right_cancel₀ h2 h1
  exact_mod_cast hY

/-- **Lemma A, steps 2-3, for three labelled corners of a triangle.** Given `α ∉ ℚπ` and that the
three corner angles (in the `p, q, r` packaging) sum to `π`, `Σ(p_i − q_i) = 0` and
`Σ(q_i + r_i) = 2`. -/
theorem lemmaA_sum {α : ℝ} (hα : Irrational (α / Real.pi))
    (p0 q0 r0 p1 q1 r1 p2 q2 r2 : ℕ)
    (hsum : cornerAngle α p0 q0 r0 + cornerAngle α p1 q1 r1 + cornerAngle α p2 q2 r2 = Real.pi) :
    ((p0 : ℤ) - q0) + ((p1 : ℤ) - q1) + ((p2 : ℤ) - q2) = 0 ∧
      (q0 + r0) + (q1 + r1) + (q2 + r2) = 2 := by
  rw [cornerAngle_eq, cornerAngle_eq, cornerAngle_eq] at hsum
  set D : ℤ := ((p0 : ℤ) - q0) + ((p1 : ℤ) - q1) + ((p2 : ℤ) - q2) with hDdef
  set Y : ℕ := (q0 + r0) + (q1 + r1) + (q2 + r2) with hYdef
  have heq : (D : ℝ) * α + (Y : ℝ) * (Real.pi / 2) = Real.pi := by
    rw [hDdef, hYdef]
    push_cast
    push_cast at hsum
    linarith [hsum]
  exact dy_eq_of_sum hα D Y heq

/-! ## Step 4: "facts used in both patterns" -/

/-- **`y = 0` forces `A = p·α`, `p ≥ 1`** (Lemma A step 4, first bullet). -/
theorem corner_y_zero {p q r : ℕ} (hpos : 1 ≤ p + q + r) (hy : q + r = 0) :
    q = 0 ∧ r = 0 ∧ 1 ≤ p := by omega

/-- **`y = 2` structural bound**: `q ≤ 2`, no angle bound needed. -/
theorem corner_y_two_q_le {q r : ℕ} (hy : q + r = 2) : q ≤ 2 := by omega

/-- **`y = 2` and `A < π` forces `p < q`** (Lemma A step 4, second bullet: "`y_i = 2`
and `A_i < π` force `p_i < q_i ≤ 2`"; the `q ≤ 2` half is `corner_y_two_q_le`). -/
theorem corner_y_two_lt {α : ℝ} (hαpos : 0 < α) {p q r : ℕ} (hy : q + r = 2)
    (hlt : cornerAngle α p q r < Real.pi) : p < q := by
  by_contra hpq
  push_neg at hpq
  rw [cornerAngle_eq] at hlt
  have hYr : (((q + r : ℕ)) : ℝ) = 2 := by exact_mod_cast hy
  rw [hYr] at hlt
  have h2 : (2 : ℝ) * (Real.pi / 2) = Real.pi := by ring
  rw [h2] at hlt
  have hd : (0 : ℝ) ≤ (((p : ℤ) - (q : ℤ) : ℤ) : ℝ) := by
    have h : (0 : ℤ) ≤ (p : ℤ) - (q : ℤ) := by omega
    exact_mod_cast h
  nlinarith [hlt, hd, hαpos]

/-- **`y = 1` forces `q ≤ 1`, so `p − q ≥ −1`** (Lemma A step 4, third bullet). -/
theorem corner_y_one (p : ℕ) {q r : ℕ} (hy : q + r = 1) :
    q ≤ 1 ∧ (-1 : ℤ) ≤ (p : ℤ) - q := by
  constructor <;> omega

/-! ## Step 5: Pattern (2,0,0) — closed, one leaf -/

/-- **Pattern (2,0,0)** (Lemma A step 5): if corner 0 carries `y = 2`
and corners 1, 2 carry `y = 0` (and are non-vacuous: `p_i + q_i + r_i ≥ 1`), with the global
`Σ(p_i − q_i) = 0` from `lemmaA_sum` and corner 0's angle `< π`, then the angles are exactly
`(2β, α, α)`. This needs `hαpos` only (not `α ∉ ℚπ`): the case split, once `hy0/hy1/hy2` and `hD` are
in hand, is pure integer arithmetic plus the `< π` bound. -/
theorem patternA_core {α : ℝ} (hαpos : 0 < α)
    (p0 q0 r0 p1 q1 r1 p2 q2 r2 : ℕ)
    (hpos1 : 1 ≤ p1 + q1 + r1) (hpos2 : 1 ≤ p2 + q2 + r2)
    (hy0 : q0 + r0 = 2) (hy1 : q1 + r1 = 0) (hy2 : q2 + r2 = 0)
    (hD : ((p0 : ℤ) - q0) + ((p1 : ℤ) - q1) + ((p2 : ℤ) - q2) = 0)
    (hlt0 : cornerAngle α p0 q0 r0 < Real.pi) :
    cornerAngle α p0 q0 r0 = 2 * (Real.pi / 2 - α) ∧
      cornerAngle α p1 q1 r1 = α ∧ cornerAngle α p2 q2 r2 = α := by
  obtain ⟨hq1, hr1, hp1⟩ := corner_y_zero hpos1 hy1
  obtain ⟨hq2, hr2, hp2⟩ := corner_y_zero hpos2 hy2
  have hlt0' : p0 < q0 := corner_y_two_lt hαpos hy0 hlt0
  have hq0le : q0 ≤ 2 := corner_y_two_q_le hy0
  have key : p0 = 0 ∧ q0 = 2 ∧ p1 = 1 ∧ p2 = 1 := by
    subst hq1; subst hq2
    omega
  obtain ⟨hp0, hq0, hp1', hp2'⟩ := key
  refine ⟨?_, ?_, ?_⟩
  · rw [cornerAngle_eq]
    have hYr : (((q0 + r0 : ℕ)) : ℝ) = 2 := by exact_mod_cast hy0
    have hpq : ((((p0 : ℤ) - (q0 : ℤ) : ℤ)) : ℝ) = -2 := by
      have h : (p0 : ℤ) - (q0 : ℤ) = -2 := by rw [hp0, hq0]; norm_num
      exact_mod_cast h
    rw [hYr, hpq]; ring
  · rw [cornerAngle_eq]
    have hYr : (((q1 + r1 : ℕ)) : ℝ) = 0 := by exact_mod_cast hy1
    have hpq : ((((p1 : ℤ) - (q1 : ℤ) : ℤ)) : ℝ) = 1 := by
      have h : (p1 : ℤ) - (q1 : ℤ) = 1 := by rw [hp1', hq1]; norm_num
      exact_mod_cast h
    rw [hYr, hpq]; ring
  · rw [cornerAngle_eq]
    have hYr : (((q2 + r2 : ℕ)) : ℝ) = 0 := by exact_mod_cast hy2
    have hpq : ((((p2 : ℤ) - (q2 : ℤ) : ℤ)) : ℝ) = 1 := by
      have h : (p2 : ℤ) - (q2 : ℤ) = 1 := by rw [hp2', hq2]; norm_num
      exact_mod_cast h
    rw [hYr, hpq]; ring

/-! ## Step 6: Pattern (1,1,0) — closed, all three sub-leaves -/

/-- **Pattern (1,1,0)** (Lemma A step 6): if corners 0, 1 carry `y = 1`
and corner 2 carries `y = 0` (non-vacuous), with the global `Σ(p_i − q_i) = 0`, then exactly one of:
* `p₃ = 1` (here, corner 2's `p`): angles `(β, π/2, α)`, i.e. ABC similar to T;
* `p₃ = 2`: angles `(β, β, 2α)`.
`p₃ ≥ 3` is excluded automatically (it is not one of the disjuncts, matching the argument's
"`p_3 ≥ 3` is impossible"): the integer system `d0 + d1 + d2 = 0`, `d0, d1 ≥ −1`, `d2 = p2 ≥ 1`
(from `corner_y_zero`) forces `d2 ≤ 2`, so no third case exists to omit. This needs no angle bound
(`hlt`) at all — only the structural facts and `hD`, matching step 6, which cites
no `A_i < π` fact for this pattern. -/
theorem patternB_core
    (p0 q0 r0 p1 q1 r1 p2 q2 r2 : ℕ)
    (hpos2 : 1 ≤ p2 + q2 + r2)
    (hy0 : q0 + r0 = 1) (hy1 : q1 + r1 = 1) (hy2 : q2 + r2 = 0)
    (hD : ((p0 : ℤ) - q0) + ((p1 : ℤ) - q1) + ((p2 : ℤ) - q2) = 0)
    (α : ℝ) :
    (cornerAngle α p0 q0 r0 = Real.pi / 2 - α ∧ cornerAngle α p1 q1 r1 = Real.pi / 2 ∧
        cornerAngle α p2 q2 r2 = α) ∨
      (cornerAngle α p0 q0 r0 = Real.pi / 2 ∧ cornerAngle α p1 q1 r1 = Real.pi / 2 - α ∧
        cornerAngle α p2 q2 r2 = α) ∨
      (cornerAngle α p0 q0 r0 = Real.pi / 2 - α ∧ cornerAngle α p1 q1 r1 = Real.pi / 2 - α ∧
        cornerAngle α p2 q2 r2 = 2 * α) := by
  -- Work directly with the integer differences `d_i = p_i − q_i`: `y_i = 0`/`y_i = 1` pin `y_i·π/2`
  -- but do NOT uniquely pin `(p_i, q_i)` individually when `d_i = 0` (e.g. `(p,q) = (0,0)` and
  -- `(1,1)` both give `d = 0`) — only `d_i` matters for the angle, so that is what is case-split.
  obtain ⟨hq0le, hb0⟩ := corner_y_one p0 hy0
  obtain ⟨hq1le, hb1⟩ := corner_y_one p1 hy1
  obtain ⟨hq2, hr2, hp2⟩ := corner_y_zero hpos2 hy2
  have angle0 : cornerAngle α p0 q0 r0 = (((p0 : ℤ) - (q0 : ℤ) : ℤ) : ℝ) * α + Real.pi / 2 := by
    rw [cornerAngle_eq]
    have hYr : (((q0 + r0 : ℕ)) : ℝ) = 1 := by exact_mod_cast hy0
    rw [hYr]; ring
  have angle1 : cornerAngle α p1 q1 r1 = (((p1 : ℤ) - (q1 : ℤ) : ℤ) : ℝ) * α + Real.pi / 2 := by
    rw [cornerAngle_eq]
    have hYr : (((q1 + r1 : ℕ)) : ℝ) = 1 := by exact_mod_cast hy1
    rw [hYr]; ring
  have angle2 : cornerAngle α p2 q2 r2 = (((p2 : ℤ) - (q2 : ℤ) : ℤ) : ℝ) * α := by
    rw [cornerAngle_eq]
    have hYr : (((q2 + r2 : ℕ)) : ℝ) = 0 := by exact_mod_cast hy2
    rw [hYr]; ring
  have hd2 : (p2 : ℤ) - (q2 : ℤ) = (p2 : ℤ) := by rw [hq2]; ring
  have hd2pos : (1 : ℤ) ≤ (p2 : ℤ) - (q2 : ℤ) := by rw [hd2]; exact_mod_cast hp2
  -- `d0 + d1 + d2 = 0`, `d0 ≥ -1`, `d1 ≥ -1`, `d2 ≥ 1` forces exactly this 3-way split
  -- (step 6: `p3 = 1` splits into two symmetric sub-leaves; `p3 = 2` is the third;
  -- `p3 ≥ 3` is excluded, matching that no fourth disjunct exists here).
  have hcase :
      ((p0 : ℤ) - q0 = -1 ∧ (p1 : ℤ) - q1 = 0 ∧ (p2 : ℤ) - q2 = 1) ∨
        ((p0 : ℤ) - q0 = 0 ∧ (p1 : ℤ) - q1 = -1 ∧ (p2 : ℤ) - q2 = 1) ∨
        ((p0 : ℤ) - q0 = -1 ∧ (p1 : ℤ) - q1 = -1 ∧ (p2 : ℤ) - q2 = 2) := by
    omega
  rcases hcase with ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩
  · left
    refine ⟨?_, ?_, ?_⟩
    · rw [angle0, e0]; push_cast; ring
    · rw [angle1, e1]; push_cast; ring
    · rw [angle2, e2]; push_cast; ring
  · right; left
    refine ⟨?_, ?_, ?_⟩
    · rw [angle0, e0]; push_cast; ring
    · rw [angle1, e1]; push_cast; ring
    · rw [angle2, e2]; push_cast; ring
  · right; right
    refine ⟨?_, ?_, ?_⟩
    · rw [angle0, e0]; push_cast; ring
    · rw [angle1, e1]; push_cast; ring
    · rw [angle2, e2]; push_cast; ring

/-! ## Lemma A itself: the six-way case split over which corner carries which pattern

The case split is over *which* of the three named corners plays which role (the (2,0,0) pattern's
special corner can be corner 0, 1 or 2; likewise the (1,1,0) pattern's `y = 0` corner). Together with
`patternA_core`/`patternB_core`, this gives Lemma A's conclusion exactly as stated:
"ABC is similar to T, or has angles (α, α, π−2α), or has angles (β, β, π−2β)." -/

/-- **Lemma A's case split, in full**, given Step 1's corner-fact hypothesis (an arbitrary abstract
`(p, q, r)` triple per corner — NOT derived from any real `CongruentDissection`, see the file header).
Concludes the shape is one of: similar to T (`α, β, π/2`, in some order), `(2β, α, α)`
(some order), or `(β, β, 2α)` (some order) — Lemma A's own three shapes, `π − 2α = 2β` and
`π − 2β = 2α` unfolded. -/
theorem lemmaA_case_split {α : ℝ} (hα : Irrational (α / Real.pi)) (hαpos : 0 < α)
    (p0 q0 r0 p1 q1 r1 p2 q2 r2 : ℕ)
    (hpos0 : 1 ≤ p0 + q0 + r0) (hpos1 : 1 ≤ p1 + q1 + r1) (hpos2 : 1 ≤ p2 + q2 + r2)
    (hsum : cornerAngle α p0 q0 r0 + cornerAngle α p1 q1 r1 + cornerAngle α p2 q2 r2 = Real.pi)
    (hlt0 : cornerAngle α p0 q0 r0 < Real.pi) (hlt1 : cornerAngle α p1 q1 r1 < Real.pi)
    (hlt2 : cornerAngle α p2 q2 r2 < Real.pi) :
    -- Pattern (2,0,0), any of the three corners carrying `y = 2`:
    (cornerAngle α p0 q0 r0 = 2 * (Real.pi / 2 - α) ∧ cornerAngle α p1 q1 r1 = α ∧
        cornerAngle α p2 q2 r2 = α) ∨
      (cornerAngle α p1 q1 r1 = 2 * (Real.pi / 2 - α) ∧ cornerAngle α p0 q0 r0 = α ∧
        cornerAngle α p2 q2 r2 = α) ∨
      (cornerAngle α p2 q2 r2 = 2 * (Real.pi / 2 - α) ∧ cornerAngle α p0 q0 r0 = α ∧
        cornerAngle α p1 q1 r1 = α) ∨
    -- Pattern (1,1,0), any of the three corners carrying `y = 0` (each with two sub-leaves):
      (cornerAngle α p0 q0 r0 = Real.pi / 2 - α ∧ cornerAngle α p1 q1 r1 = Real.pi / 2 ∧
        cornerAngle α p2 q2 r2 = α) ∨
      (cornerAngle α p0 q0 r0 = Real.pi / 2 ∧ cornerAngle α p1 q1 r1 = Real.pi / 2 - α ∧
        cornerAngle α p2 q2 r2 = α) ∨
      (cornerAngle α p0 q0 r0 = Real.pi / 2 - α ∧ cornerAngle α p1 q1 r1 = Real.pi / 2 - α ∧
        cornerAngle α p2 q2 r2 = 2 * α) ∨
      (cornerAngle α p1 q1 r1 = Real.pi / 2 - α ∧ cornerAngle α p2 q2 r2 = Real.pi / 2 ∧
        cornerAngle α p0 q0 r0 = α) ∨
      (cornerAngle α p1 q1 r1 = Real.pi / 2 ∧ cornerAngle α p2 q2 r2 = Real.pi / 2 - α ∧
        cornerAngle α p0 q0 r0 = α) ∨
      (cornerAngle α p1 q1 r1 = Real.pi / 2 - α ∧ cornerAngle α p2 q2 r2 = Real.pi / 2 - α ∧
        cornerAngle α p0 q0 r0 = 2 * α) ∨
      (cornerAngle α p0 q0 r0 = Real.pi / 2 - α ∧ cornerAngle α p2 q2 r2 = Real.pi / 2 ∧
        cornerAngle α p1 q1 r1 = α) ∨
      (cornerAngle α p0 q0 r0 = Real.pi / 2 ∧ cornerAngle α p2 q2 r2 = Real.pi / 2 - α ∧
        cornerAngle α p1 q1 r1 = α) ∨
      (cornerAngle α p0 q0 r0 = Real.pi / 2 - α ∧ cornerAngle α p2 q2 r2 = Real.pi / 2 - α ∧
        cornerAngle α p1 q1 r1 = 2 * α) := by
  obtain ⟨hD, hY⟩ := lemmaA_sum hα p0 q0 r0 p1 q1 r1 p2 q2 r2 hsum
  set y0 := q0 + r0 with hy0def
  set y1 := q1 + r1 with hy1def
  set y2 := q2 + r2 with hy2def
  have hypat : (y0 = 2 ∧ y1 = 0 ∧ y2 = 0) ∨ (y1 = 2 ∧ y0 = 0 ∧ y2 = 0) ∨
      (y2 = 2 ∧ y0 = 0 ∧ y1 = 0) ∨ (y0 = 0 ∧ y1 = 1 ∧ y2 = 1) ∨
      (y1 = 0 ∧ y0 = 1 ∧ y2 = 1) ∨ (y2 = 0 ∧ y0 = 1 ∧ y1 = 1) := by omega
  rcases hypat with ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ |
    ⟨e0, e1, e2⟩
  · -- (y0=2,y1=0,y2=0): disjunct 1
    left
    exact patternA_core hαpos p0 q0 r0 p1 q1 r1 p2 q2 r2 hpos1 hpos2 e0 e1 e2 hD hlt0
  · -- (y1=2,y0=0,y2=0): disjunct 2
    right; left
    exact patternA_core hαpos p1 q1 r1 p0 q0 r0 p2 q2 r2 hpos0 hpos2 e0 e1 e2 (by linarith [hD])
      hlt1
  · -- (y2=2,y0=0,y1=0): disjunct 3
    right; right; left
    exact patternA_core hαpos p2 q2 r2 p0 q0 r0 p1 q1 r1 hpos0 hpos1 e0 e1 e2 (by linarith [hD])
      hlt2
  · -- (y0=0,y1=1,y2=1): corner 0 is the `y=0` role; feed patternB_core (p1,p2,p0) → disjuncts 7-9
    have hD1 : ((p1 : ℤ) - q1) + ((p2 : ℤ) - q2) + ((p0 : ℤ) - q0) = 0 := by linarith [hD]
    rcases patternB_core p1 q1 r1 p2 q2 r2 p0 q0 r0 hpos0 e1 e2 e0 hD1 α with h | h | h
    · right; right; right; right; right; right; left; exact h
    · right; right; right; right; right; right; right; left; exact h
    · right; right; right; right; right; right; right; right; left; exact h
  · -- (y1=0,y0=1,y2=1): corner 1 is the `y=0` role; feed patternB_core (p0,p2,p1) → disjuncts 10-12
    have hD2 : ((p0 : ℤ) - q0) + ((p2 : ℤ) - q2) + ((p1 : ℤ) - q1) = 0 := by linarith [hD]
    rcases patternB_core p0 q0 r0 p2 q2 r2 p1 q1 r1 hpos1 e1 e2 e0 hD2 α with h | h | h
    · right; right; right; right; right; right; right; right; right; left; exact h
    · right; right; right; right; right; right; right; right; right; right; left; exact h
    · right; right; right; right; right; right; right; right; right; right; right; exact h
  · -- (y2=0,y0=1,y1=1): corner 2 is the `y=0` role; feed patternB_core (p0,p1,p2) → disjuncts 4-6
    rcases patternB_core p0 q0 r0 p1 q1 r1 p2 q2 r2 hpos2 e1 e2 e0 hD α with h | h | h
    · right; right; right; left; exact h
    · right; right; right; right; left; exact h
    · right; right; right; right; right; left; exact h

/-! ## Non-vacuity witnesses -/

/-- Witness angle: `α = π·(√2/10)`, so `α/π = √2/10` is irrational and `0 < α < π/2`. Reuses
`irrational_sqrt_two` (Mathlib) via `Irrational.div_natCast`, not reproved. -/
theorem lemmaA_witness_alpha_irrational :
    Irrational ((Real.pi * (Real.sqrt 2 / 10)) / Real.pi) := by
  have h : (Real.pi * (Real.sqrt 2 / 10)) / Real.pi = Real.sqrt 2 / 10 := by
    field_simp
  rw [h]
  have h10 : Irrational (Real.sqrt 2 / ((10 : ℕ) : ℝ)) :=
    irrational_sqrt_two.div_natCast (by norm_num)
  simpa using h10

theorem lemmaA_witness_alpha_pos : 0 < Real.pi * (Real.sqrt 2 / 10) := by
  have h1 : (0:ℝ) < Real.sqrt 2 / 10 := by positivity
  exact mul_pos Real.pi_pos h1

theorem lemmaA_witness_alpha_lt : Real.pi * (Real.sqrt 2 / 10) < Real.pi / 2 := by
  have hs : Real.sqrt 2 < 2 := by
    have h2 : (Real.sqrt 2) ^ 2 < 2 ^ 2 := by
      rw [Real.sq_sqrt (by norm_num : (2:ℝ) ≥ 0)]; norm_num
    nlinarith [Real.sqrt_nonneg (2:ℝ)]
  nlinarith [Real.pi_pos, hs]

/-- **Non-vacuity witness for `patternA_core`'s full hypothesis bundle**: the pattern (2,0,0) data
`(p,q,r) = (0,2,0), (1,0,0), (1,0,0)`, at `α = π·(√2/10)`. Every hypothesis (`hpos1`, `hpos2`, the
three `hy`'s, `hD`, and `hlt0`) is checked directly, not assumed; the conclusion is `(2β, α, α)`. -/
theorem patternA_core_witness :
    cornerAngle (Real.pi * (Real.sqrt 2 / 10)) 0 2 0 =
        2 * (Real.pi / 2 - Real.pi * (Real.sqrt 2 / 10)) ∧
      cornerAngle (Real.pi * (Real.sqrt 2 / 10)) 1 0 0 = Real.pi * (Real.sqrt 2 / 10) ∧
      cornerAngle (Real.pi * (Real.sqrt 2 / 10)) 1 0 0 = Real.pi * (Real.sqrt 2 / 10) := by
  apply patternA_core lemmaA_witness_alpha_pos 0 2 0 1 0 0 1 0 0
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · have h1 : cornerAngle (Real.pi * (Real.sqrt 2 / 10)) 0 2 0 =
        2 * (Real.pi / 2 - Real.pi * (Real.sqrt 2 / 10)) := by
      unfold cornerAngle; push_cast; ring
    rw [h1]
    nlinarith [lemmaA_witness_alpha_lt, lemmaA_witness_alpha_pos]

/-- **Non-vacuity witness for `patternB_core`'s hypothesis bundle**, sub-leaf `p₃ = 1` (similar to
T): data `(0,1,0), (1,1,0), (1,0,0)` (`D = (-1, 0, 1)`; note the middle corner needs `r = 0, q = 1`
*or* `q = 0, r = 1` — either represents `D₁ = 0`; `(1,1,0)` is used here). Ruled out via a direct
algebraic mismatch (`α ≠ 0`), not via any numeric bound on `α`. -/
theorem patternB_core_witness_similar :
    cornerAngle (Real.pi * (Real.sqrt 2 / 10)) 0 1 0 = Real.pi / 2 - Real.pi * (Real.sqrt 2 / 10) ∧
      cornerAngle (Real.pi * (Real.sqrt 2 / 10)) 1 1 0 = Real.pi / 2 ∧
      cornerAngle (Real.pi * (Real.sqrt 2 / 10)) 1 0 0 = Real.pi * (Real.sqrt 2 / 10) := by
  have h := patternB_core 0 1 0 1 1 0 1 0 0 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (Real.pi * (Real.sqrt 2 / 10))
  have hane : Real.pi * (Real.sqrt 2 / 10) ≠ 0 := ne_of_gt lemmaA_witness_alpha_pos
  rcases h with h | h | h
  · exact h
  · exfalso
    obtain ⟨-, hb, -⟩ := h
    have h1 : cornerAngle (Real.pi * (Real.sqrt 2 / 10)) 1 1 0 = Real.pi / 2 := by
      unfold cornerAngle; push_cast; ring
    rw [h1] at hb
    apply hane
    linarith [hb]
  · exfalso
    obtain ⟨-, hb, -⟩ := h
    have h1 : cornerAngle (Real.pi * (Real.sqrt 2 / 10)) 1 1 0 = Real.pi / 2 := by
      unfold cornerAngle; push_cast; ring
    rw [h1] at hb
    apply hane
    linarith [hb]

/-- **Non-vacuity witness**, sub-leaf `p₃ = 2` (`(β,β,2α)`): data `(0,1,0), (0,1,0), (2,0,0)`
(`D = (-1,-1,2)`). -/
theorem patternB_core_witness_isosceles :
    cornerAngle (Real.pi * (Real.sqrt 2 / 10)) 0 1 0 = Real.pi / 2 - Real.pi * (Real.sqrt 2 / 10) ∧
      cornerAngle (Real.pi * (Real.sqrt 2 / 10)) 0 1 0 = Real.pi / 2 - Real.pi * (Real.sqrt 2 / 10) ∧
      cornerAngle (Real.pi * (Real.sqrt 2 / 10)) 2 0 0 = 2 * (Real.pi * (Real.sqrt 2 / 10)) := by
  have h := patternB_core 0 1 0 0 1 0 2 0 0 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (Real.pi * (Real.sqrt 2 / 10))
  have hane : Real.pi * (Real.sqrt 2 / 10) ≠ 0 := ne_of_gt lemmaA_witness_alpha_pos
  rcases h with h | h | h
  · exfalso
    obtain ⟨-, hb, -⟩ := h
    have h1 : cornerAngle (Real.pi * (Real.sqrt 2 / 10)) 0 1 0 =
        Real.pi / 2 - Real.pi * (Real.sqrt 2 / 10) := by unfold cornerAngle; push_cast; ring
    rw [h1] at hb
    apply hane
    linarith [hb]
  · exfalso
    obtain ⟨ha, -, -⟩ := h
    have h1 : cornerAngle (Real.pi * (Real.sqrt 2 / 10)) 0 1 0 =
        Real.pi / 2 - Real.pi * (Real.sqrt 2 / 10) := by unfold cornerAngle; push_cast; ring
    rw [h1] at ha
    apply hane
    linarith [ha]
  · exact h

/-- **Non-vacuity witness for `lemmaA_case_split`'s full hypothesis bundle**: the pattern (2,0,0)
data `(0,2,0), (1,0,0), (1,0,0)`, with `α`'s irrationality (`lemmaA_witness_alpha_irrational`) now
actually used, and all three angle bounds and the sum checked directly. Every hypothesis of
`lemmaA_case_split` is discharged concretely (`hα`, `hαpos`, the three `hpos`'s, `hsum`, the three
`hlt`'s); the conclusion is the theorem's first disjunct, ruled in (not merely "some disjunct holds")
by matching it against the concrete computed angle values, exactly as `patternA_core_witness` does. -/
theorem lemmaA_case_split_witness :
    cornerAngle (Real.pi * (Real.sqrt 2 / 10)) 0 2 0 =
        2 * (Real.pi / 2 - Real.pi * (Real.sqrt 2 / 10)) ∧
      cornerAngle (Real.pi * (Real.sqrt 2 / 10)) 1 0 0 = Real.pi * (Real.sqrt 2 / 10) ∧
      cornerAngle (Real.pi * (Real.sqrt 2 / 10)) 1 0 0 = Real.pi * (Real.sqrt 2 / 10) := by
  have hsum : cornerAngle (Real.pi * (Real.sqrt 2 / 10)) 0 2 0 +
      cornerAngle (Real.pi * (Real.sqrt 2 / 10)) 1 0 0 +
      cornerAngle (Real.pi * (Real.sqrt 2 / 10)) 1 0 0 = Real.pi := by
    unfold cornerAngle; push_cast; ring
  have hlt0 : cornerAngle (Real.pi * (Real.sqrt 2 / 10)) 0 2 0 < Real.pi := by
    have h1 : cornerAngle (Real.pi * (Real.sqrt 2 / 10)) 0 2 0 =
        2 * (Real.pi / 2 - Real.pi * (Real.sqrt 2 / 10)) := by unfold cornerAngle; push_cast; ring
    rw [h1]; nlinarith [lemmaA_witness_alpha_lt, lemmaA_witness_alpha_pos]
  have hlt1 : cornerAngle (Real.pi * (Real.sqrt 2 / 10)) 1 0 0 < Real.pi := by
    have h1 : cornerAngle (Real.pi * (Real.sqrt 2 / 10)) 1 0 0 =
        Real.pi * (Real.sqrt 2 / 10) := by unfold cornerAngle; push_cast; ring
    rw [h1]; nlinarith [lemmaA_witness_alpha_lt, Real.pi_pos]
  have h := lemmaA_case_split lemmaA_witness_alpha_irrational lemmaA_witness_alpha_pos
    0 2 0 1 0 0 1 0 0 (by norm_num) (by norm_num) (by norm_num) hsum hlt0 hlt1 hlt1
  have hα1 : cornerAngle (Real.pi * (Real.sqrt 2 / 10)) 1 0 0 =
      Real.pi * (Real.sqrt 2 / 10) := by unfold cornerAngle; push_cast; ring
  have hα0 : cornerAngle (Real.pi * (Real.sqrt 2 / 10)) 0 2 0 =
      2 * (Real.pi / 2 - Real.pi * (Real.sqrt 2 / 10)) := by unfold cornerAngle; push_cast; ring
  -- **The robust closing device**: every disjunct other than the first forces, once combined with
  -- `hα0`/`hα1`, an equation `(n:ℝ) * α = π` for `n ∈ {2, 3, 4}` — i.e. `α` would be a *rational*
  -- multiple of `π`, contradicting `lemmaA_witness_alpha_irrational` directly (no numeric bound on
  -- `α` is needed, unlike an `nlinarith`-with-π-bounds approach, which is fragile because several
  -- branches solve to *different* rational multiples of `π` and no single bound rules all of them
  -- out at once).
  have hno_rat : ∀ n : ℤ, n ≠ 0 → (n : ℝ) * (Real.pi * (Real.sqrt 2 / 10)) = Real.pi → False := by
    intro n hn heq
    apply irrational_sqrt_two
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    have heq' : (n : ℝ) * (Real.sqrt 2 / 10) * Real.pi = 1 * Real.pi := by
      have hring : (n : ℝ) * (Real.pi * (Real.sqrt 2 / 10)) = (n : ℝ) * (Real.sqrt 2 / 10) * Real.pi := by
        ring
      rw [← hring]; simpa using heq
    have hstep : (n : ℝ) * (Real.sqrt 2 / 10) = 1 :=
      mul_right_cancel₀ Real.pi_ne_zero heq'
    have hstep2 : (n : ℝ) * Real.sqrt 2 = 10 := by
      field_simp at hstep; linarith [hstep]
    refine ⟨(10 : ℚ) / (n : ℚ), ?_⟩
    rw [Rat.cast_div]
    push_cast
    rw [div_eq_iff hn']
    linarith [hstep2]
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · exact h
  · exact absurd (by obtain ⟨-, hb, -⟩ := h; rw [hα0] at hb; linarith [hb] :
      (3 : ℝ) * (Real.pi * (Real.sqrt 2 / 10)) = Real.pi) (fun e => hno_rat 3 (by norm_num) e)
  · exact absurd (by obtain ⟨-, hb, -⟩ := h; rw [hα0] at hb; linarith [hb] :
      (3 : ℝ) * (Real.pi * (Real.sqrt 2 / 10)) = Real.pi) (fun e => hno_rat 3 (by norm_num) e)
  · exact absurd (by obtain ⟨ha, -, -⟩ := h; rw [hα0] at ha; linarith [ha] :
      (2 : ℝ) * (Real.pi * (Real.sqrt 2 / 10)) = Real.pi) (fun e => hno_rat 2 (by norm_num) e)
  · exact absurd (by obtain ⟨ha, -, -⟩ := h; rw [hα0] at ha; linarith [ha] :
      (4 : ℝ) * (Real.pi * (Real.sqrt 2 / 10)) = Real.pi) (fun e => hno_rat 4 (by norm_num) e)
  · exact absurd (by obtain ⟨ha, -, -⟩ := h; rw [hα0] at ha; linarith [ha] :
      (2 : ℝ) * (Real.pi * (Real.sqrt 2 / 10)) = Real.pi) (fun e => hno_rat 2 (by norm_num) e)
  · exact absurd (by obtain ⟨-, -, hc⟩ := h; rw [hα0] at hc; linarith [hc] :
      (3 : ℝ) * (Real.pi * (Real.sqrt 2 / 10)) = Real.pi) (fun e => hno_rat 3 (by norm_num) e)
  · exact absurd (by obtain ⟨-, -, hc⟩ := h; rw [hα0] at hc; linarith [hc] :
      (3 : ℝ) * (Real.pi * (Real.sqrt 2 / 10)) = Real.pi) (fun e => hno_rat 3 (by norm_num) e)
  · exact absurd (by obtain ⟨-, -, hc⟩ := h; rw [hα0] at hc; linarith [hc] :
      (4 : ℝ) * (Real.pi * (Real.sqrt 2 / 10)) = Real.pi) (fun e => hno_rat 4 (by norm_num) e)
  · exact absurd (by obtain ⟨ha, -, -⟩ := h; rw [hα0] at ha; linarith [ha] :
      (2 : ℝ) * (Real.pi * (Real.sqrt 2 / 10)) = Real.pi) (fun e => hno_rat 2 (by norm_num) e)
  · exact absurd (by obtain ⟨ha, -, -⟩ := h; rw [hα0] at ha; linarith [ha] :
      (4 : ℝ) * (Real.pi * (Real.sqrt 2 / 10)) = Real.pi) (fun e => hno_rat 4 (by norm_num) e)
  · exact absurd (by obtain ⟨ha, -, -⟩ := h; rw [hα0] at ha; linarith [ha] :
      (2 : ℝ) * (Real.pi * (Real.sqrt 2 / 10)) = Real.pi) (fun e => hno_rat 2 (by norm_num) e)

end Erdos634.Geometry.Row3

#print axioms Erdos634.Geometry.Row3.cornerAngle_eq
#print axioms Erdos634.Geometry.Row3.dy_eq_of_sum
#print axioms Erdos634.Geometry.Row3.lemmaA_sum
#print axioms Erdos634.Geometry.Row3.corner_y_zero
#print axioms Erdos634.Geometry.Row3.corner_y_two_q_le
#print axioms Erdos634.Geometry.Row3.corner_y_two_lt
#print axioms Erdos634.Geometry.Row3.corner_y_one
#print axioms Erdos634.Geometry.Row3.patternA_core
#print axioms Erdos634.Geometry.Row3.patternB_core
#print axioms Erdos634.Geometry.Row3.lemmaA_case_split
#print axioms Erdos634.Geometry.Row3.lemmaA_witness_alpha_irrational
#print axioms Erdos634.Geometry.Row3.patternA_core_witness
#print axioms Erdos634.Geometry.Row3.patternB_core_witness_similar
#print axioms Erdos634.Geometry.Row3.patternB_core_witness_isosceles
#print axioms Erdos634.Geometry.Row3.lemmaA_case_split_witness
