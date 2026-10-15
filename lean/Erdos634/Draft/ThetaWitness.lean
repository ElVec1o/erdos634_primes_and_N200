/-
Draft/ThetaWitness.lean  In `AllThreshold`.  Witnesses and controls for S7, S8, S9 (project rule: a theorem whose hypotheses are unsatisfiable proves nothing).

The two kernel-checked tilings of the library satisfy every hypothesis of the theorems of `SideRunGThetaMain` and `ThetaKill`:
* `θ_4(1,2)`: `FDCCevianAtom.atomTiles_four_scaled`, a congruent dissection with 48 tiles, target sides `(12, 24, 24)`, tile `(2, 3, 4)`: `(t, e, f) = (4, 1, 2)`, legs `t f b = 24`, base `t e b = 12`.
  S7 (`theta_word_hasSides`, `s = 4`) gives a base word `12 = 2x + 3y + 4z` with `z ≥ 2`; S8 (`theta_te_ge`) gives `2 f = 4 ≤ t e = 4`: the bound is ATTAINED, so `t e ≥ 2 f` cannot be improved at `(1, 2)`; S9 (`theta_e1`) gives `t ≥ 2 f = 4`
  and `f⁴ = 16 ≤ t f (f² − 1) = 24`.
* `θ_8(2,3)`: `S5N320.s5_8_2_3`, 320 tiles, target `(120, 120, 80)`, tile `(6, 5, 9)` (`5 9 6` rotated): `(t, e, f) = (8, 2, 3)`, `s = 8`.  S7 gives a base word `80 = 6x + 5y + 9z`, `z ≥ 3`; S8: `2 f = 6 ≤ t e = 16`; the thick form (`e = f − 1`):
  `f + 2 = 5 ≤ t = 8`.
* CONTROLS (the statements are not vacuous in the other direction): `s5inst_4_1_2_false` (`¬ S5Inst 4 1 2`: the instance with `t e = 2 f` is realised; `s5inst_of_te_lt_2f` cannot reach it) and `s5inst_8_2_3_false`.

No sorry, no native_decide.
-/
import Erdos634.Draft.ThetaKill
import Erdos634.Draft.FDCCevianAtom
import Erdos634.Draft.S5N320

open scoped Classical

namespace Erdos634.Draft.ThetaWitness

open Erdos634.Geometry Erdos634.Draft.NSQM
open Erdos634.Draft.FDBBaseBetaE1 (HasSides hasSides_rot)
open Erdos634.Draft.UniformThreshold (hasSides_congr)
open Erdos634.Draft.ThetaKill
open Erdos634.Draft.SideRunGT (theta_word_hasSides thm_side_theta)
open Erdos634.Draft.NSQM (s5inst_hasSides)

/-! ## `θ_4(1,2)` -/

/-- the 48-tile tiling of `θ_4(1,2)` in the form of the hypotheses of the theorems -/
theorem theta_4_1_2 : ∃ (N : ℕ) (D : CongruentDissection N),
    HasSides D.target 24 24 12 ∧ HasSides D.model 2 3 4 := by
  obtain ⟨D, hT, hM⟩ := Erdos634.Draft.FDCCevianAtom.atomTiles_four_scaled
  exact ⟨_, D, hasSides_rot hT, hM⟩

/-- S7 on `θ_4(1,2)`: a base word `12 = 2x + 3y + 4z` with `z ≥ 2` -/
theorem word_4_1_2 : ∃ x y z : ℕ, (x : ℝ) * 2 + y * 3 + z * 4 = 12 ∧ 2 ≤ z := by
  obtain ⟨N, D, hT, hM⟩ := theta_4_1_2
  obtain ⟨x, y, z, hxyz, hz⟩ := theta_word_hasSides 1 2 le_rfl (by norm_num) (by decide) (s := 4) (by norm_num) D
    (hasSides_congr hT (by norm_num) (by norm_num) (by norm_num))
    (hasSides_congr hM (by norm_num) (by norm_num) (by norm_num))
  refine ⟨x, y, z, ?_, hz⟩
  norm_num at hxyz
  linarith

/-- S8 on `θ_4(1,2)`: `2 f ≤ t e`, with equality -/
theorem te_4_1_2 : 2 * (2 : ℤ) ≤ 4 * 1 := by
  obtain ⟨N, D, hT, hM⟩ := theta_4_1_2
  exact theta_te_ge D (t := 4) (e := 1) (f := 2) (by norm_num) (by norm_num) (by norm_num) isCoprime_one_left
    (hasSides_congr hT (by norm_num) (by norm_num) (by norm_num))
    (hasSides_congr hM (by norm_num) (by norm_num) (by norm_num))

/-- S9 on `θ_4(1,2)` -/
theorem e1_4_1_2 : 2 * (2 : ℤ) ≤ 4 ∧ ((2 : ℤ) : ℝ) ^ 4 ≤ ((4 : ℤ) : ℝ) * ((2 : ℤ) : ℝ) * (((2 : ℤ) : ℝ) ^ 2 - 1) := by
  obtain ⟨N, D, hT, hM⟩ := theta_4_1_2
  exact theta_e1 D (t := 4) (f := 2) le_rfl (by norm_num)
    (hasSides_congr hT (by norm_num) (by norm_num) (by norm_num))
    (hasSides_congr hM (by norm_num) (by norm_num) (by norm_num))

/-- **Control**: `S5Inst 4 1 2` is false, the tiling realises it (`t e = 2 f`) -/
theorem s5inst_4_1_2_false : ¬ S5Inst 4 1 2 := by
  intro h
  obtain ⟨N, D, hT, hM⟩ := theta_4_1_2
  exact s5inst_hasSides h D (hasSides_congr hT (by norm_num) (by norm_num) (by norm_num))
    (hasSides_congr hM (by norm_num) (by norm_num) (by norm_num))

/-! ## `θ_8(2,3)` -/

/-- the 320-tile tiling of `θ_8(2,3)` in the form of the hypotheses of the theorems -/
theorem theta_8_2_3 : ∃ (N : ℕ) (D : CongruentDissection N),
    HasSides D.target 120 120 80 ∧ HasSides D.model 6 5 9 := by
  obtain ⟨D, hT, hM⟩ := Erdos634.Draft.S5N320.s5_8_2_3
  exact ⟨_, D, hT, hasSides_rot (hasSides_rot hM)⟩

/-- S7 on `θ_8(2,3)`: a base word `80 = 6x + 5y + 9z` with `z ≥ 3` -/
theorem word_8_2_3 : ∃ x y z : ℕ, (x : ℝ) * 6 + y * 5 + z * 9 = 80 ∧ 3 ≤ z := by
  obtain ⟨N, D, hT, hM⟩ := theta_8_2_3
  obtain ⟨x, y, z, hxyz, hz⟩ := theta_word_hasSides 2 3 (by norm_num) (by norm_num) (by decide) (s := 8) (by norm_num) D
    (hasSides_congr hT (by norm_num) (by norm_num) (by norm_num))
    (hasSides_congr hM (by norm_num) (by norm_num) (by norm_num))
  refine ⟨x, y, z, ?_, hz⟩
  norm_num at hxyz
  linarith

/-- S8 on `θ_8(2,3)`: `2 f = 6 ≤ t e = 16` -/
theorem te_8_2_3 : 2 * (3 : ℤ) ≤ 8 * 2 := by
  obtain ⟨N, D, hT, hM⟩ := theta_8_2_3
  exact theta_te_ge D (t := 8) (e := 2) (f := 3) (by norm_num) (by norm_num) (by norm_num) ⟨-1, 1, by norm_num⟩
    (hasSides_congr hT (by norm_num) (by norm_num) (by norm_num))
    (hasSides_congr hM (by norm_num) (by norm_num) (by norm_num))

/-- S8, thick form, on `θ_8(2,3)` (`e = f − 1`): `f + 2 = 5 ≤ t = 8` -/
theorem thick_8_2_3 : (3 : ℤ) + 2 ≤ 8 := by
  obtain ⟨N, D, hT, hM⟩ := theta_8_2_3
  exact theta_thick D (t := 8) (f := 3) (by norm_num) (by norm_num)
    (hasSides_congr hT (by norm_num) (by norm_num) (by norm_num))
    (hasSides_congr hM (by norm_num) (by norm_num) (by norm_num))

/-- S7 on `θ_8(2,3)` in the form of the paper: the base `[Q, B]` carries `f = 3` tiles that lay their side `c` on it (`thm_side_theta`, `s = 8`) -/
theorem side_8_2_3 : ∃ (N : ℕ) (_ : CongruentDissection N) (_ : Fin 3 × Fin 3) (x₀ : ℝ), 0 ≤ x₀ ∧ x₀ + (3 : ℝ) * (3 : ℝ) ^ 2 ≤ 80 := by
  obtain ⟨N, D, hT, hM⟩ := theta_8_2_3
  obtain ⟨k₀, k₁, x₀, -, -, -, h0, hend, -, -⟩ := thm_side_theta 2 3 (by norm_num) (by norm_num) (by decide) (s := 8) (by norm_num) D
    (hasSides_congr hT (by norm_num) (by norm_num) (by norm_num))
    (hasSides_congr hM (by norm_num) (by norm_num) (by norm_num))
  exact ⟨N, D, (k₀, k₁), x₀, h0, by norm_num at hend ⊢; linarith⟩

/-- **Control**: `S5Inst 8 2 3` is false, the tiling realises it -/
theorem s5inst_8_2_3_false : ¬ S5Inst 8 2 3 := Erdos634.Draft.S5N320.not_S5Inst_8_2_3

end Erdos634.Draft.ThetaWitness

#print axioms Erdos634.Draft.ThetaWitness.word_4_1_2
#print axioms Erdos634.Draft.ThetaWitness.te_4_1_2
#print axioms Erdos634.Draft.ThetaWitness.e1_4_1_2
#print axioms Erdos634.Draft.ThetaWitness.word_8_2_3
#print axioms Erdos634.Draft.ThetaWitness.te_8_2_3
#print axioms Erdos634.Draft.ThetaWitness.thick_8_2_3
#print axioms Erdos634.Draft.ThetaWitness.side_8_2_3
