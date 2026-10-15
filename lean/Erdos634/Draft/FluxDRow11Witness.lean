-- Draft/FluxDRow11Witness.lean: non-vacuity witnesses for Draft/FluxDRow11.lean (Theorem R11).
-- Imported by `All`.
--
-- The base-α target `(α, α, α + 2β)` has no known tiling, so `Row11.boundary_baseAlpha`,
-- `Row11.setup` and `Row11.rational` are unwitnessed at the geometric level (they are conditionals).
-- The algebraic hypotheses of L4/L5a are witnessed one at a time:
-- * `rational_branch`: `s = 1/2`, `(K, M) = (9, 5)`, leg word `3c`.  Every L5a hypothesis except
--   `s ∉ ℚ` holds (the rational tile, which R11 does not exclude); L4 evaluated: `λ = 7/2`.
-- * `model41`: `(K, M) = (1·5, 1)`, `s = (−3+√41)/4 ∉ ℚ` satisfies the equation of L3/L4; L4
--   evaluated: `λ = 3/2`; by L5a no leg word exists (it fails only the side-word condition).
-- * `model896`: `M = 40`, `s = (−8+√86)/11 ∉ ℚ`, leg word `44a + 16c`.  Every L5a hypothesis except
--   the χ₊ equation holds; by L5a no integer `K` satisfies it (it fails only the χ₊ equation).
import Erdos634.Draft.FluxDRow11

open scoped Classical

namespace Erdos634.Draft.FluxDRow11Witness

open Erdos634.Geometry

/-! ## The rational branch `s = 1/2` -/

/-- **All L5a hypotheses but irrationality, at `s = 1/2`, `K = 9`, `M = 5`, leg `3c`**; `s ∈ ℚ`. -/
theorem rational_branch : 0 < (1 / 2 : ℝ) ∧ (1 / 2 : ℝ) < 1 ∧ (1 : ℤ) ≤ 5 ∧
    ((9 : ℤ) : ℝ) * (1 - 1 / 2) * (2 + 1 / 2) = ((5 : ℤ) : ℝ) * (1 + 1 / 2) * (2 - 1 / 2) ∧
    (((0 : ℕ) : ℝ) * (1 / 2) + ((0 : ℕ) : ℝ) * (1 - (1 / 2) ^ 2) + ((3 : ℕ) : ℝ)) * (2 + 1 / 2)
      = ((5 : ℤ) : ℝ) * (1 + 1 / 2) ∧ ∃ r : ℚ, (1 / 2 : ℝ) = r := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, 1 / 2, by norm_num⟩

/-- **L4 applied at `s = 1/2`, `(K, M) = (9, 5)`**: `λ = 14/4 = 7/2`. -/
theorem L4_rational :
    (5 : ℤ) < 9 ∧ (1 / 2 : ℝ) ^ 2 + ((((9 + 5 : ℤ) : ℚ) / ((9 - 5 : ℤ) : ℚ) : ℚ) : ℝ) * (1 / 2) - 2 = 0
      ∧ (1 : ℚ) < ((9 + 5 : ℤ) : ℚ) / ((9 - 5 : ℤ) : ℚ) :=
  Row11.L4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) rational_branch.2.2.2.1

/-! ## The `(M, K) = (1, 5)` model -/

unseal Nat.sqrt.iter in
theorem irr41 : Irrational √(41 : ℝ) := by decide

/-- `s₄₁ = (−3 + √41)/4`, root of `2s² + 3s − 4 = 0`. -/
noncomputable def s41 : ℝ := (-3 + √(41 : ℝ)) / 4

theorem sqrt41_sq : √(41 : ℝ) ^ 2 = 41 := Real.sq_sqrt (by norm_num)

theorem s41_quad : 2 * s41 ^ 2 + 3 * s41 - 4 = 0 := by
  unfold s41; linear_combination (1 / 8 : ℝ) * sqrt41_sq

/-- **The `(M, K) = (1, 5)` model**: `s ∉ ℚ`, `0 < s < 1`, `5(1−s)(2+s) = 1·(1+s)(2−s)`. -/
theorem model41 : (¬ ∃ r : ℚ, s41 = r) ∧ 0 < s41 ∧ s41 < 1 ∧
    ((5 : ℤ) : ℝ) * (1 - s41) * (2 + s41) = ((1 : ℤ) : ℝ) * (1 + s41) * (2 - s41) := by
  have h0 := Real.sqrt_nonneg (41 : ℝ)
  have hsq := sqrt41_sq
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro ⟨r, hr⟩
    apply irr41
    refine ⟨4 * r + 3, ?_⟩
    push_cast
    unfold s41 at hr
    linarith
  · unfold s41; nlinarith
  · unfold s41; nlinarith
  · push_cast; linear_combination (-2 : ℝ) * s41_quad

/-- **L4 applied to the `(1, 5)` model**: `λ = 6/4 = 3/2`. -/
theorem model41_L4 :
    (1 : ℤ) < 5 ∧ s41 ^ 2 + ((((5 + 1 : ℤ) : ℚ) / ((5 - 1 : ℤ) : ℚ) : ℚ) : ℝ) * s41 - 2 = 0 ∧
      (1 : ℚ) < ((5 + 1 : ℤ) : ℚ) / ((5 - 1 : ℤ) : ℚ) :=
  Row11.L4 model41.2.1 model41.2.2.1 le_rfl (by norm_num) model41.2.2.2

/-- **By L5a the `(1, 5)` model has no leg word** (it fails only W). -/
theorem model41_no_word (na nb nc : ℕ) :
    (na * s41 + nb * (1 - s41 ^ 2) + nc) * (2 + s41) ≠ ((1 : ℤ) : ℝ) * (1 + s41) :=
  fun hw => Row11.L5a model41.1 model41.2.1 model41.2.2.1 le_rfl model41.2.2.2 hw

/-! ## The `N = 896`, `M = 40` model -/

unseal Nat.sqrt.iter in
theorem irr86 : Irrational √(86 : ℝ) := by decide

/-- `s₈₆ = (−8 + √86)/11`, root of `11s² + 16s − 2 = 0`. -/
noncomputable def s86 : ℝ := (-8 + √(86 : ℝ)) / 11

theorem sqrt86_sq : √(86 : ℝ) ^ 2 = 86 := Real.sq_sqrt (by norm_num)

theorem s86_quad : 11 * s86 ^ 2 + 16 * s86 - 2 = 0 := by
  unfold s86; linear_combination (1 / 11 : ℝ) * sqrt86_sq

/-- **The `N = 896` model**: `s ∉ ℚ`, `0 < s < 1`, `M = 40 ≥ 1`, and the leg word `44a + 16c`:
`(44 s + 0·(1−s²) + 16)(2+s) = 40(1+s)`. -/
theorem model896 : (¬ ∃ r : ℚ, s86 = r) ∧ 0 < s86 ∧ s86 < 1 ∧ (1 : ℤ) ≤ 40 ∧
    (((44 : ℕ) : ℝ) * s86 + ((0 : ℕ) : ℝ) * (1 - s86 ^ 2) + ((16 : ℕ) : ℝ)) * (2 + s86)
      = ((40 : ℤ) : ℝ) * (1 + s86) := by
  have h0 := Real.sqrt_nonneg (86 : ℝ)
  have hsq := sqrt86_sq
  refine ⟨?_, ?_, ?_, by norm_num, ?_⟩
  · rintro ⟨r, hr⟩
    apply irr86
    refine ⟨11 * r + 8, ?_⟩
    push_cast
    unfold s86 at hr
    linarith
  · unfold s86; nlinarith
  · unfold s86; nlinarith
  · push_cast; linear_combination 4 * s86_quad

/-- **By L5a no integer `K` satisfies the χ₊ equation on the `896` model** (it fails only χ₊). -/
theorem model896_no_K (K : ℤ) :
    (K : ℝ) * (1 - s86) * (2 + s86) ≠ ((40 : ℤ) : ℝ) * (1 + s86) * (2 - s86) :=
  fun hK => Row11.L5a model896.1 model896.2.1 model896.2.2.1 model896.2.2.2.1 hK model896.2.2.2.2

end Erdos634.Draft.FluxDRow11Witness

#print axioms Erdos634.Draft.FluxDRow11Witness.rational_branch
#print axioms Erdos634.Draft.FluxDRow11Witness.L4_rational
#print axioms Erdos634.Draft.FluxDRow11Witness.model41
#print axioms Erdos634.Draft.FluxDRow11Witness.model41_L4
#print axioms Erdos634.Draft.FluxDRow11Witness.model41_no_word
#print axioms Erdos634.Draft.FluxDRow11Witness.model896
#print axioms Erdos634.Draft.FluxDRow11Witness.model896_no_K
