/-
Draft/PI3HStripArith.lean -- the strip lemma, ARITHMETIC statements only (hypothesis-free real lemmas).

The real-number content of the strip lemma that needs no geometry:
* `strip_arith_sound` : the integer predicate (I) of `stripI` implies the REAL inequality `r * M < 4N`, `M = (s + sqrt D)/2`,
                        `r = 2N - l_kappa`, i.e. `L0 = S - 4N/M < l_kappa` at `S = 2N`.  Soundness of (I) w.r.t. reals.
* `stripI_sound`      : the same for `stripI N (xdata N x) = true`.
* `strip_real_609/2145/6693` : the three kills, as real inequalities, obtained from the kernel results of `PI3HArithKill`.
* `sl1_corrected`     : the corrected (non-strict) strip inequality `d >= m - M tan(phi)` fed into SL2: from it, a chord whose endpoint
                        heights satisfy the three-height identity has `L (sqrt3 cos phi + sin phi) <= sqrt3 S - 2 H` (SL2, pure algebra).
* `lb_le_of_ge`       : `Lb <= L0` follows from the cross-multiplied inequality.

Not included (geometry; nothing here is a geometric theorem):
  SL1 itself (needs "no edge point is interior to a tile", "width of a triangle >= altitude 2 Area/M", convex separation),
  the three heights `h1+h2+h3 = sqrt3 S/2` of an arbitrary equilateral `Tri` and the foot of the perpendicular lying in the side,
  chains, the existence of an unbalanced chain, and the real-analysis part SL3 (monotonicity of the (II') inequality in phi).
No sorry, no native_decide.
-/
import Erdos634.Draft.PI3HArithKill
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Erdos634.Draft.PI3H

/-- Soundness of the exact integer predicate (I): `r s < 8N` and `D r^2 < (8N - r s)^2` give `r (s + sqrt D) < 8N`. -/
theorem strip_arith_sound (N lk s D : ℕ) (hl : lk ≤ 2 * N) (h1 : (2 * N - lk) * s < 8 * N)
    (h2 : D * ((2 * N - lk) * (2 * N - lk)) < (8 * N - (2 * N - lk) * s) * (8 * N - (2 * N - lk) * s)) :
    ((2 * N : ℝ) - lk) * (((s : ℝ) + Real.sqrt D) / 2) < 4 * N := by
  have hr : (((2 * N - lk : ℕ)) : ℝ) = 2 * N - lk := by
    rw [Nat.cast_sub hl]; push_cast; ring
  have hX : (((8 * N - (2 * N - lk) * s : ℕ)) : ℝ) = 8 * N - ((2 * N - lk : ℕ) : ℝ) * s := by
    rw [Nat.cast_sub h1.le]; push_cast; ring
  have h2r : (D : ℝ) * (((2 * N - lk : ℕ) : ℝ) * ((2 * N - lk : ℕ) : ℝ)) <
      (((8 * N - (2 * N - lk) * s : ℕ)) : ℝ) * (((8 * N - (2 * N - lk) * s : ℕ)) : ℝ) := by exact_mod_cast h2
  have h1r : (((2 * N - lk : ℕ)) : ℝ) * s < 8 * N := by exact_mod_cast h1
  set r : ℝ := (((2 * N - lk : ℕ)) : ℝ) with hrdef
  set X : ℝ := 8 * N - r * s with hXdef
  rw [hX] at h2r
  have hX0 : 0 < X := by rw [hXdef]; linarith
  have hr0 : 0 ≤ r := by rw [hrdef]; positivity
  have hsq : (Real.sqrt D * r) * (Real.sqrt D * r) < X * X := by
    have : Real.sqrt D * Real.sqrt D = D := Real.mul_self_sqrt (by positivity)
    nlinarith [this]
  have hlt : Real.sqrt D * r < X := by
    by_contra hc
    push_neg at hc
    nlinarith [mul_self_nonneg (Real.sqrt D * r), Real.sqrt_nonneg (D : ℝ), mul_nonneg (Real.sqrt_nonneg (D : ℝ)) hr0]
  rw [← hr]
  nlinarith [hlt, hXdef]

/-- `stripI` (the Bool predicate) is sound for the real inequality `L0 < l_kappa` in the form `r M < 4N`. -/
theorem stripI_sound (N x : ℕ) (h : stripI N (xdata N x) = true) :
    ((2 * N : ℝ) - (xdata N x).lk) * ((((xdata N x).s : ℝ) + Real.sqrt (xdata N x).D) / 2) < 4 * N := by
  unfold stripI at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hl, h1⟩, h2⟩ := h
  exact strip_arith_sound N _ _ _ hl h1 h2

/-- The three strip kills, as real inequalities `r M < 4N` (equivalently `S - 4N/M < l_kappa`, `S = 2N`). -/
theorem strip_real_609 : (2 * (609 : ℝ) - 1188) * (((108 : ℝ) + Real.sqrt 1920) / 2) < 4 * 609 := by
  have h := stripI_sound 609 7 (by have := strip_609; unfold stripDead at this; simp only [Bool.and_eq_true] at this; exact this.1)
  have e1 : (xdata 609 7).lk = 1188 := by decide +kernel
  have e2 : (xdata 609 7).s = 108 := by decide +kernel
  have e3 : (xdata 609 7).D = 1920 := by decide +kernel
  rw [e1, e2, e3] at h; push_cast at h; exact h

theorem strip_real_2145 : (2 * (2145 : ℝ) - 4284) * (((204 : ℝ) + Real.sqrt 7296) / 2) < 4 * 2145 := by
  have h := stripI_sound 2145 13 (by have := strip_2145; unfold stripDead at this; simp only [Bool.and_eq_true] at this; exact this.1)
  have e1 : (xdata 2145 13).lk = 4284 := by decide +kernel
  have e2 : (xdata 2145 13).s = 204 := by decide +kernel
  have e3 : (xdata 2145 13).D = 7296 := by decide +kernel
  rw [e1, e2, e3] at h; push_cast at h; exact h

theorem strip_real_6693 : (2 * (6693 : ℝ) - 13320) * (((360 : ℝ) + Real.sqrt 22512) / 2) < 4 * 6693 := by
  have h := stripI_sound 6693 23 (by have := strip_6693; unfold stripDead at this; simp only [Bool.and_eq_true] at this; exact this.1)
  have e1 : (xdata 6693 23).lk = 13320 := by decide +kernel
  have e2 : (xdata 6693 23).s = 360 := by decide +kernel
  have e3 : (xdata 6693 23).D = 22512 := by decide +kernel
  rw [e1, e2, e3] at h; push_cast at h; exact h

/-- `r M < 4N` with `M > 0` is `S - 4N/M < l_kappa` at `S = 2N`. -/
theorem L0_lt_of_rM (N lk M : ℝ) (hM : 0 < M) (h : (2 * N - lk) * M < 4 * N) : 2 * N - 4 * N / M < lk := by
  have : 4 * N / M > 2 * N - lk := by rw [gt_iff_lt, lt_div_iff₀ hM]; exact h
  linarith

/-- **SL2, pure algebra, with the CORRECTED (non-strict) SL1.**  Let `h1, h2, h3` be the heights of the endpoint `E1` over the three
sides (`h1 + h2 + h3 = sqrt3 S / 2`, all `>= 0`), `E2 = E1 + L v` a point of the target, `c = cos phi`, `s = sin phi`, `s2 >= 0`, `s3 = -(sqrt3/2) c - s/2`.
If `h1 >= H` (consequence of SL1 in the NON-strict form `d >= m - M tan phi` at the point `P1`, `H = max(0, m - 2 M tan phi)`),
and `h3 + s3 L >= 0`, then `L (sqrt3 c + s) <= sqrt3 S - 2H`. -/
theorem sl2_algebra (S H L h1 h2 h3 c s r3 : ℝ) (hr3 : r3 * r3 = 3) (hr3p : 0 < r3)
    (hsum : h1 + h2 + h3 = r3 * S / 2) (hh1 : H ≤ h1) (hh2 : 0 ≤ h2)
    (hh3 : (r3 / 2 * c + s / 2) * L ≤ h3) :
    L * (r3 * c + s) ≤ r3 * S - 2 * H := by
  nlinarith [hsum, hh1, hh2, hh3]

/-- SL1 (corrected) -> `h1(E1) >= H`: if the point `P1 = E1 + (M/cos phi) v` has height `>= m - M tan phi` and heights grow along `v` at rate
`sin phi`, then `h1(E1) + M tan phi >= m - M tan phi`, hence `h1(E1) >= m - 2 M tan phi`. (Strict version not needed.) -/
theorem sl1_corrected (h1E1 hP1 m M t : ℝ) (hP : hP1 = h1E1 + M * t) (hs : m - M * t ≤ hP1) : m - 2 * M * t ≤ h1E1 := by
  linarith

/-- `Lb <= L0` from the cross-multiplied inequality (the denominator `sqrt3 c + s` is positive). -/
theorem lb_le_of_ge (num den L0 : ℝ) (hden : 0 < den) (h : num ≤ L0 * den) : num / den ≤ L0 := by
  rw [div_le_iff₀ hden]; exact h

end Erdos634.Draft.PI3H

#print axioms Erdos634.Draft.PI3H.strip_arith_sound
#print axioms Erdos634.Draft.PI3H.stripI_sound
#print axioms Erdos634.Draft.PI3H.strip_real_609
#print axioms Erdos634.Draft.PI3H.strip_real_2145
#print axioms Erdos634.Draft.PI3H.strip_real_6693
#print axioms Erdos634.Draft.PI3H.sl2_algebra
