-- Draft/FluxFRow14.lean: on the scalene target `(2α, β, α+β)`, an `N`-tiling (any `N`, reflections
-- allowed, not necessarily edge-to-edge) by the `3α + 2β = π` tile with `α ∉ ℚπ` has a rational tile,
-- `s := a/c ∈ ℚ`.
--
-- The argument is pure algebra over ℚ(s): a coefficient-matching and linear-independence argument plus
-- the fact that every side carries a `c`-edge (F4). It does not use the flux functional, `GridChar`, or
-- `fAlpha`/`fBeta`; it uses only the word of a single side and the irrationality of `α`.
--
-- Scope.
-- Unconditional: `rat_coeff_unique` (the `{1,s}`-independence step) and `nonneg_sum_forces_zero`
-- (elementary nonnegativity) are general algebraic facts.
-- Conditional at the algebraic level: `row14_word_to_std_form` packages the tiling word equation
-- `n_a·s + n_b·(1−t) + n_c = M·(1−t)/t·s` (with `t = s² = 2/(q+1)`) into the shape `r·s + c0 = 0` that
-- `rat_coeff_unique` consumes; `row14_rational` combines these: the word equation together with F4
-- (`nc ≥ 1`, every side carries a `c`-edge) gives `s ∈ ℚ`.
-- Not formalized in this file: the derivation that `t = 2/(q+1)` is `s²` from the boundary evaluation and
-- the area identity (`q = N/M²`), and the geometric content of F2 (why the corner-angle multiset forces a
-- side with this word) and F4 (why every side has a `c`-edge, Beeson III Lemma 5). These enter as
-- hypotheses `hF4` and the shape of `hword`, not derived from a `CongruentDissection`.
--
-- Non-vacuity. `rat_coeff_unique` and `nonneg_sum_forces_zero` have no hypothesis to witness. The
-- hypotheses of `row14_rational` are jointly satisfiable: `row14_witness_s_half` exhibits `s = 1/2` (so
-- `NotRat s` is false and the conclusion `¬ NotRat s` holds trivially) together with the integer word
-- `(n_a,n_b,n_c) = (1,0,1)`, `M = T = 1` satisfying `hword` and `hF4`. The model `s = 1/√2` (irrational)
-- has words without a `c`-edge on this side (`nc = 0`), which is why F4 fails there.
import Mathlib.Tactic


open scoped Classical

namespace Erdos634.Row14

/-- Local stand-in for Mathlib's `Irrational`: `s` is not the image
of any rational. Same content, different name. -/
def NotRat (s : ℝ) : Prop := ¬ ∃ q : ℚ, s = (q : ℝ)

/-- **`{1, s}`-independence when `s` is irrational** (§2 step 2, "Suppose `s ∉ Q`. Then `1` and
`s` are `Q`-independent"). If `r·s + c0 = 0` with `r, c0 : ℚ` and `s` is irrational, then
`r = 0` and `c0 = 0`. -/
theorem rat_coeff_unique {s : ℝ} (hs : NotRat s) (r c0 : ℚ)
    (heq : (r : ℝ) * s + (c0 : ℝ) = 0) : r = 0 ∧ c0 = 0 := by
  by_cases hr : r = 0
  · refine ⟨hr, ?_⟩
    subst hr
    have h0 : (c0 : ℝ) = 0 := by simpa using heq
    exact_mod_cast h0
  · exfalso
    apply hs
    have hr' : (r : ℝ) ≠ 0 := by exact_mod_cast hr
    have hsr : s * (r : ℝ) = -(c0 : ℝ) := by nlinarith [heq]
    refine ⟨-c0 / r, ?_⟩
    have hseq : s = -(c0 : ℝ) / (r : ℝ) := by
      rw [eq_div_iff hr']; linarith [hsr]
    rw [hseq]; push_cast; ring

/-- **Elementary nonnegativity** (part of §2 step 4): if `b > 0` and `nb·b + nc = 0` with
`nb, nc : ℕ`, then `nb = 0` and `nc = 0`. -/
theorem nonneg_sum_forces_zero {b : ℝ} (hb : 0 < b) (nb nc : ℕ)
    (heq : (nb : ℝ) * b + (nc : ℝ) = 0) : nb = 0 ∧ nc = 0 := by
  have hnb0 : (0:ℝ) ≤ (nb : ℝ) * b := mul_nonneg (Nat.cast_nonneg _) hb.le
  have hnc0 : (0:ℝ) ≤ (nc : ℝ) := Nat.cast_nonneg _
  have h1 : (nb : ℝ) * b = 0 := by linarith
  have h2 : (nc : ℝ) = 0 := by linarith
  have hnb : (nb : ℝ) = 0 := by
    rcases mul_eq_zero.mp h1 with h | h
    · exact h
    · exact absurd h hb.ne'
  exact ⟨by exact_mod_cast hnb, by exact_mod_cast h2⟩

/-- The `r`-coefficient of the word equation packaged into `ℚ` (see `row14_word_to_std_form`). -/
def rCoeff (na M : ℤ) (T : ℚ) : ℚ := (na : ℚ) - (M : ℚ) * (1 - T) / T

/-- The constant coefficient of the word equation packaged into `ℚ`. -/
def c0Coeff (nb nc : ℕ) (T : ℚ) : ℚ := (nb : ℚ) * (1 - T) + (nc : ℚ)

/-- **The word equation, in `r·s + c0 = 0` form** (§2 steps 1, 3–4). The side `Y` opposite the
single-tile `β` corner carries word `n_a·a + n_b·b + n_c·c` (`F3`); with `a = s, b = 1 − t, c = 1`
(`t = s²`) and `Y = M·(1−t)/t · s` (the tiling equation, `t = 2/(q+1) ∈ Q`, here packaged as the
rational number `T`), this is `r·s + c0 = 0` with `r = n_a − M·(1−T)/T` and
`c0 = n_b·(1−T) + n_c`, both manifestly rational since `n_a, n_b, n_c, M ∈ ℤ` and `T ∈ ℚ`. -/
theorem row14_word_to_std_form (s t : ℝ) (T : ℚ) (ht : t = (T : ℝ)) (ht0 : T ≠ 0)
    (na M : ℤ) (nb nc : ℕ)
    (hword : (na : ℝ) * s + (nb : ℝ) * (1 - t) + (nc : ℝ) = (M : ℝ) * (1 - t) / t * s) :
    (rCoeff na M T : ℝ) * s + (c0Coeff nb nc T : ℝ) = 0 := by
  have hT0 : (T : ℝ) ≠ 0 := by exact_mod_cast ht0
  have key : ((na : ℝ) - (M : ℝ) * (1 - t) / t) * s + ((nb : ℝ) * (1 - t) + (nc : ℝ)) = 0 := by
    linear_combination hword
  have hcast : (rCoeff na M T : ℝ) = (na : ℝ) - (M : ℝ) * (1 - t) / t := by
    unfold rCoeff; rw [ht]; push_cast; ring
  have hcast0 : (c0Coeff nb nc T : ℝ) = (nb : ℝ) * (1 - t) + (nc : ℝ) := by
    unfold c0Coeff; rw [ht]; push_cast; ring
  rw [hcast, hcast0]; exact key

/-- **Row 14's F4 contradiction, assembled** (steps 1–5 in full): if `s`
is irrational, the word equation holds (`t = s²` rational, packaged as `T`), and `F4` holds on
this side (`1 ≤ nc`, "the side carries a `c`-edge"), then `False`. Equivalently, contrapositive:
under the word equation and F4, `s` cannot be irrational, i.e. `s ∈ ℚ`. -/
theorem row14_rational (s t : ℝ) (T : ℚ) (ht : t = (T : ℝ)) (ht0 : T ≠ 0)
    (ht1 : (0:ℝ) < 1 - t) (na M : ℤ) (nb nc : ℕ)
    (hword : (na : ℝ) * s + (nb : ℝ) * (1 - t) + (nc : ℝ) = (M : ℝ) * (1 - t) / t * s)
    (hF4 : 1 ≤ nc) : ¬ NotRat s := by
  intro hs
  have hstd := row14_word_to_std_form s t T ht ht0 na M nb nc hword
  obtain ⟨_, hc0⟩ := rat_coeff_unique hs (rCoeff na M T) (c0Coeff nb nc T) hstd
  have ht1' : (0:ℝ) < 1 - (T:ℝ) := ht ▸ ht1
  have hc0' : (nb : ℝ) * (1 - (T:ℝ)) + (nc : ℝ) = 0 := by
    have : (c0Coeff nb nc T : ℝ) = 0 := by exact_mod_cast hc0
    unfold c0Coeff at this; push_cast at this; linarith
  have hz := nonneg_sum_forces_zero (b := (1 - (T:ℝ))) ht1' nb nc hc0'
  omega

/-- **Non-vacuity witness**: the hypothesis bundle of `row14_rational` (word equation + `F4`) is
satisfiable — at `s = 1/2` (`NotRat s` false, so the conclusion is trivial there, but the
*hypotheses* are real numbers satisfying real equations, not `False → False`): `t = T = 1/4`,
`(n_a, n_b, n_c) = (1, 0, 1)`, `M = 1` satisfy `n_a·s + n_b·(1−t) + n_c = M·(1−t)/t·s`
(`1·(1/2) + 0 + 1 = 3/2 = 1·(3/4)/(1/4)·(1/2)`) and `F4` (`nc = 1 ≥ 1`). -/
theorem row14_witness_s_half :
    ((1:ℤ) : ℝ) * (1/2 : ℝ) + ((0:ℕ):ℝ) * (1 - (1/4:ℝ)) + ((1:ℕ):ℝ)
        = ((1:ℤ):ℝ) * (1 - (1/4:ℝ)) / (1/4:ℝ) * (1/2 : ℝ)
    ∧ (1:ℕ) ≤ (1:ℕ) := by
  constructor
  · norm_num
  · exact le_refl 1

end Erdos634.Row14

#print axioms Erdos634.Row14.rat_coeff_unique
#print axioms Erdos634.Row14.nonneg_sum_forces_zero
#print axioms Erdos634.Row14.row14_word_to_std_form
#print axioms Erdos634.Row14.row14_rational
#print axioms Erdos634.Row14.row14_witness_s_half
