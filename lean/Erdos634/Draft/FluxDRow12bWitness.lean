-- Draft/FluxDRow12bWitness.lean: non-vacuity witnesses for Draft/FluxDSideWord.lean (side words) and
-- Draft/FluxDRow12b.lean (cases 12(a), 12(b)).  Imported by `All`.
--
-- * Side words on the 44- and 99-tilings: legs `128`, `384` and bases `176`, `528` are words in the
--   tile sides `(16, 24, 32)`, `(32, 48, 64)` (`CongruentDissection.side_word_threeAlpha`).
-- * `Row12.setup` on the 44- and 99-tilings, evaluated: `s = 1/2`, `M = 6` (N = 44) and
--   `M = 9` (N = 99), the tiling quadratic holding at `s = 1/2`.
-- * `Row12.case_a` (`M² < N`) applied on both tilings: `36 < 44`, `81 < 99`; its conclusion
--   (`a/c ∈ ℚ`) is reached through the theorem (the tile is `(2,3,4)`).
-- * `Row12.leg_coeff`, `Row12.base_coeff` with an irrational `s`: the model `N = 15`, `M = 5`,
--   `s = (−3+√105)/8`, leg word `a + 4b + c`, base word `b + 5c` (all hypotheses proved).  Their
--   conclusions evaluate to `1600 = 40²` and `150 = 15·(25−15)`; `M ∣ N²` (5 ∣ 225) holds there, which
--   is why primality is needed in 12(b).
-- * `Row12.prime_rational` (12(b)): every hypothesis except `N.Prime` is met on the 44/99 tilings.
--   No instance with prime `N` is known (the existence of one is the open base-β question), so the
--   full hypothesis set of 12(b) is unwitnessed.
import Erdos634.Draft.FluxDRow12b
import Erdos634.Draft.FluxRow11Witness
import Erdos634.Draft.FluxCWitness99

open scoped Classical

namespace Erdos634.Draft.FluxDRow12bWitness

open Erdos634.Geometry Erdos634.Draft.FluxGridWitness

/-! ## W on the real 44- and 99-tilings -/

/-- **W on the real 44-tiling**: the leg `128` and the base `176` are words in `(16, 24, 32)`. -/
theorem words_44 : (∃ na nb nc : ℕ, (128 : ℝ) = na * 16 + nb * 24 + nc * 32) ∧
    (∃ na nb nc : ℕ, (176 : ℝ) = na * 16 + nb * 24 + nc * 32) := by
  obtain ⟨na, nb, nc, h0⟩ := Erdos634.Tiling44Bridge.dissection.side_word_threeAlpha
    Erdos634.Draft.FluxRow11Witness.data44 0
  obtain ⟨ma, mb, mc, h2⟩ := Erdos634.Tiling44Bridge.dissection.side_word_threeAlpha
    Erdos634.Draft.FluxRow11Witness.data44 2
  change Erdos634.Tiling44Bridge.targetTri.oppLen 0 = _ at h0
  change Erdos634.Tiling44Bridge.targetTri.oppLen 2 = _ at h2
  rw [t_opp.1] at h0
  rw [t_opp.2.2] at h2
  exact ⟨⟨na, nb, nc, h0⟩, ⟨ma, mb, mc, h2⟩⟩

/-- **W on the real 99-tiling**: the leg `384` and the base `528` are words in `(32, 48, 64)`. -/
theorem words_99 : (∃ na nb nc : ℕ, (384 : ℝ) = na * 32 + nb * 48 + nc * 64) ∧
    (∃ na nb nc : ℕ, (528 : ℝ) = na * 32 + nb * 48 + nc * 64) := by
  obtain ⟨na, nb, nc, h0⟩ := Erdos634.Tiling99Bridge.dissection.side_word_threeAlpha
    Erdos634.Draft.FluxCWitness99.data99 0
  obtain ⟨ma, mb, mc, h2⟩ := Erdos634.Tiling99Bridge.dissection.side_word_threeAlpha
    Erdos634.Draft.FluxCWitness99.data99 2
  change Erdos634.Tiling99Bridge.targetTri.oppLen 0 = _ at h0
  change Erdos634.Tiling99Bridge.targetTri.oppLen 2 = _ at h2
  rw [Erdos634.Draft.FluxCWitness99.t99_opp.1] at h0
  rw [Erdos634.Draft.FluxCWitness99.t99_opp.2.2] at h2
  exact ⟨⟨na, nb, nc, h0⟩, ⟨ma, mb, mc, h2⟩⟩

/-! ## `Row12.setup` and 12(a) on the real tilings -/

/-- **`Row12.setup` on the real 44-tiling, evaluated**: `s = 1/2`, `M = 6`, and the tiling quadratic
`(44 + M²)s² + 88 s + (44 − 3M²) = 0` holds. -/
theorem setup_44 : ∃ (s : ℝ) (M : ℤ), s = 1 / 2 ∧ M = 6 ∧
    ((44 : ℝ) + (M : ℝ) ^ 2) * s ^ 2 + 2 * 44 * s + (44 - 3 * (M : ℝ) ^ 2) = 0 := by
  obtain ⟨s, M, -, -, -, ha, -, -, -, -, hMid, -, -, hq⟩ :=
    Row12.setup Erdos634.Tiling44Bridge.dissection α44_irr three_α_two_β
      Erdos634.Draft.FluxRow11Witness.data44 t_angle0 t_angle1
  rw [Erdos634.Tiling44Bridge.tiles_length_eq_44] at hq
  change (M : ℝ) * (16 + 24 + 32) = Erdos634.Tiling44Bridge.targetTri.oppLen 2
    + 2 * Erdos634.Tiling44Bridge.targetTri.oppLen 0 at hMid
  rw [t_opp.2.2, t_opp.1] at hMid
  have eM : (M : ℝ) = 6 := by linarith
  refine ⟨s, M, by linarith, by exact_mod_cast eM, ?_⟩
  push_cast at hq
  exact hq

/-- **12(a) applied on the real 44-tiling**: `M = 6`, `M² = 36 < 44`, so `a/c ∈ ℚ` by `Row12.case_a`. -/
theorem case_a_44 : ∃ r : ℚ, (16 : ℝ) = (r : ℝ) * 32 := by
  obtain ⟨M, -, hMid, hcase⟩ := Row12.case_a Erdos634.Tiling44Bridge.dissection α44_irr
    three_α_two_β Erdos634.Draft.FluxRow11Witness.data44 t_angle0 t_angle1
  apply hcase
  change (M : ℝ) * (16 + 24 + 32) = Erdos634.Tiling44Bridge.targetTri.oppLen 2
    + 2 * Erdos634.Tiling44Bridge.targetTri.oppLen 0 at hMid
  rw [t_opp.2.2, t_opp.1] at hMid
  have eM : (M : ℝ) = 6 := by linarith
  have hM6 : M = 6 := by exact_mod_cast eM
  rw [Erdos634.Tiling44Bridge.tiles_length_eq_44, hM6]
  norm_num

/-- **12(a) applied on the real 99-tiling**: `M = 9`, `M² = 81 < 99`. -/
theorem case_a_99 : ∃ r : ℚ, (32 : ℝ) = (r : ℝ) * 64 := by
  obtain ⟨M, -, hMid, hcase⟩ := Row12.case_a Erdos634.Tiling99Bridge.dissection α44_irr
    three_α_two_β Erdos634.Draft.FluxCWitness99.data99 Erdos634.Draft.FluxCWitness99.t99_angle0
    Erdos634.Draft.FluxCWitness99.t99_angle1
  apply hcase
  change (M : ℝ) * (32 + 48 + 64) = Erdos634.Tiling99Bridge.targetTri.oppLen 2
    + 2 * Erdos634.Tiling99Bridge.targetTri.oppLen 0 at hMid
  rw [Erdos634.Draft.FluxCWitness99.t99_opp.2.2, Erdos634.Draft.FluxCWitness99.t99_opp.1] at hMid
  have eM : (M : ℝ) = 9 := by linarith
  have hM9 : M = 9 := by exact_mod_cast eM
  rw [Erdos634.Tiling99Bridge.tiles_length_eq_99, hM9]
  norm_num

/-! ## The s-coordinate lemmas with an irrational `s` (review 2b's `N = 15`, `M = 5` model) -/

unseal Nat.sqrt.iter in
theorem irr105 : Irrational √(105 : ℝ) := by decide

/-- `s₁₅ = (−3 + √105)/8`, the root of `4s² + 3s − 6 = 0` (`q = 15/25`). -/
noncomputable def s15 : ℝ := (-3 + √(105 : ℝ)) / 8

theorem s15_irr : ¬ ∃ r : ℚ, s15 = r := by
  rintro ⟨r, hr⟩
  apply irr105
  refine ⟨8 * r + 3, ?_⟩
  push_cast
  unfold s15 at hr
  linarith

theorem sqrt105_sq : √(105 : ℝ) ^ 2 = 105 := Real.sq_sqrt (by norm_num)

theorem s15_pos : 0 < s15 := by
  unfold s15
  nlinarith [Real.sqrt_nonneg (105 : ℝ), sqrt105_sq]

theorem s15_quad : 4 * s15 ^ 2 + 3 * s15 - 6 = 0 := by
  unfold s15
  linear_combination (1 / 16 : ℝ) * sqrt105_sq

/-- **`Row12.leg_coeff`'s and `Row12.base_coeff`'s hypotheses, jointly, with `s ∉ ℚ`**: the tiling
quadratic at `(N, M) = (15, 5)`, the leg word `a + 4b + c` and the base word `b + 5c`. -/
theorem model15_hyps : (¬ ∃ r : ℚ, s15 = r) ∧ 0 < s15 ∧
    (((15 : ℕ) : ℝ) + ((5 : ℤ) : ℝ) ^ 2) * s15 ^ 2 + 2 * ((15 : ℕ) : ℝ) * s15
      + (((15 : ℕ) : ℝ) - 3 * ((5 : ℤ) : ℝ) ^ 2) = 0 ∧
    (1 + s15) * (((1 : ℕ) : ℝ) * s15 + ((4 : ℕ) : ℝ) * (1 - s15 ^ 2) + ((1 : ℕ) : ℝ))
      = ((5 : ℤ) : ℝ) ∧
    (1 + s15) * (((0 : ℕ) : ℝ) * s15 + ((1 : ℕ) : ℝ) * (1 - s15 ^ 2) + ((5 : ℕ) : ℝ))
      = ((5 : ℤ) : ℝ) * s15 * (3 - s15 ^ 2) := by
  have hq := s15_quad
  refine ⟨s15_irr, s15_pos, ?_, ?_, ?_⟩
  · push_cast; linear_combination 10 * hq
  · push_cast; linear_combination (-s15) * hq
  · push_cast; linear_combination (s15 - 1) * hq

/-- `Row12.leg_coeff` evaluated on the model: `2·5·40·1 + 4·5·15·4 = 40²`. -/
theorem leg_coeff_15 :
    2 * (5 : ℤ) * ((15 : ℕ) + (5 : ℤ) ^ 2) * ((1 : ℕ) : ℤ) + 4 * (5 : ℤ) * ((15 : ℕ) : ℤ) * ((4 : ℕ) : ℤ)
      = (((15 : ℕ) : ℤ) + (5 : ℤ) ^ 2) ^ 2 :=
  Row12.leg_coeff s15_irr s15_pos model15_hyps.2.2.1 model15_hyps.2.2.2.1

/-- `Row12.base_coeff` evaluated on the model: `5·40·0 + 2·5·15·1 = 15·(25 − 15)`. -/
theorem base_coeff_15 :
    (5 : ℤ) * ((15 : ℕ) + (5 : ℤ) ^ 2) * ((0 : ℕ) : ℤ) + 2 * (5 : ℤ) * ((15 : ℕ) : ℤ) * ((1 : ℕ) : ℤ)
      = ((15 : ℕ) : ℤ) * ((5 : ℤ) ^ 2 - (15 : ℕ)) :=
  Row12.base_coeff s15_irr s15_pos model15_hyps.2.2.1 model15_hyps.2.2.2.2

end Erdos634.Draft.FluxDRow12bWitness

#print axioms Erdos634.Draft.FluxDRow12bWitness.words_44
#print axioms Erdos634.Draft.FluxDRow12bWitness.words_99
#print axioms Erdos634.Draft.FluxDRow12bWitness.setup_44
#print axioms Erdos634.Draft.FluxDRow12bWitness.case_a_44
#print axioms Erdos634.Draft.FluxDRow12bWitness.case_a_99
#print axioms Erdos634.Draft.FluxDRow12bWitness.model15_hyps
#print axioms Erdos634.Draft.FluxDRow12bWitness.leg_coeff_15
#print axioms Erdos634.Draft.FluxDRow12bWitness.base_coeff_15
