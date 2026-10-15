-- Draft/FDCConicFormPi3Wit.lean — non-vacuity witnesses for `FDCConicFormPi3` on REAL certified
-- dissections of equilateral targets (kernel-checked BSP certificates, `G3CCert`).
--   π/3 half : `G3CSixtyControl.D`, N = 1440, equilateral side 806400 = 240·3360, tile (5,8,7)·3360,
--              7 opposite π/3, `cos α = 11/14` (irrational angle).
--   2π/3 half: `G3CEqui135Control.D`, N = 1215, equilateral side 135·1890, tile (3,5,7)·1890.
-- Every hypothesis of `eqspecint_sixty` / `conicform_pi3_of_tiling` / `conicform_2pi3_of_tiling_full`
-- is discharged by existing Lean on these real dissections; the integers produced are pinned.
import Erdos634.Draft.FDCConicFormPi3
import Erdos634.Draft.G3CSixtyControl
import Erdos634.Draft.G3CEqui135Control

namespace Erdos634.Draft.FDCConicFormPi3Wit

open Erdos634.Geometry Erdos634.Draft.FDCConicFormPi3

open Erdos634.Draft.G3CSixtyControl in
/-- π/3 half on the certified 1440-tiling: `eqspecint_sixty` applies and pins
`m₁ = 120`, `m₂ = 36`, `q = 36` (`120·36 = 3·1440`; `156² − 16·1440 = 36²`). -/
theorem sixty_values_1440 : ∃ m₁ m₂ q : ℤ, m₁ = 120 ∧ m₂ = 36 ∧ q = 36 := by
  have hS : ∀ k, D.target.oppLen k = 806400 := by
    intro k
    fin_cases k
    · exact t_opp0
    · exact t_opp1
    · exact t_opp2
  obtain ⟨m₁, m₂, q, -, -, -, -, hm1d, hm2d, hqd, -, -, -, -⟩ :=
    eqspecint_sixty D α_irr data
      ⟨16800, 26880, 23520, by norm_num, by norm_num, by norm_num⟩ t_angle hS
  have e1 : (m₁ : ℝ) = 120 := by rw [hm1d]; norm_num
  have e2 : (m₂ : ℝ) = 36 := by rw [hm2d]; norm_num
  have hneg : (2 * 806400 * (3360 * 5 - 3360 * 8) / (3360 * 5 * (3360 * 8)) : ℝ) = -36 := by
    norm_num
  have e3 : (q : ℝ) = 36 := by
    rw [hqd, hneg, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 36)]
  exact ⟨m₁, m₂, q, by exact_mod_cast e1, by exact_mod_cast e2, by exact_mod_cast e3⟩

open Erdos634.Draft.G3CSixtyControl in
/-- π/3 half, full conclusion, on the certified 1440-tiling (the hypotheses of
`conicform_pi3_of_tiling` are satisfied by a real dissection; `N = 1440` by `cert_len`). -/
theorem conicform_pi3_real_1440 :
    ∃ u v M : ℤ, u * v = 16 * (1440 : ℤ) ^ 2 ∧ (2 : ℤ) ∣ (u + v) ∧
      (u + v) / 2 = 5 * (1440 : ℤ) - M ^ 2 ∧ 0 < M ∧ M ^ 2 < 1440 ∧ (2 : ℤ) ∣ M - 1440 := by
  have hS : ∀ k, D.target.oppLen k = 806400 := by
    intro k
    fin_cases k
    · exact t_opp0
    · exact t_opp1
    · exact t_opp2
  obtain ⟨u, v, M, h1, h2, h3, h4, h5, h6⟩ :=
    conicform_pi3_of_tiling D α_irr data
      ⟨16800, 26880, 23520, by norm_num, by norm_num, by norm_num⟩ t_angle hS
  have hN : (Erdos634.Draft.G3CEqui60n1440.cert.leaves.length : ℤ) = 1440 := by
    exact_mod_cast Erdos634.Draft.G3CEqui60n1440.cert_len
  refine ⟨u, v, M, by rw [← hN]; exact h1, h2, by rw [← hN]; exact h3, h4, ?_, by rw [← hN]; exact h6⟩
  have hM2 : (M : ℝ) ^ 2 < (1440 : ℝ) := by
    have := (Real.lt_sqrt (by exact_mod_cast h4.le)).mp h5
    rw [show (1440 : ℝ) = ((Erdos634.Draft.G3CEqui60n1440.cert.leaves.length : ℕ) : ℝ) by
      exact_mod_cast Erdos634.Draft.G3CEqui60n1440.cert_len.symm]
    exact this
  exact_mod_cast hM2

/-- Arithmetic instance behind the real 1440-tiling: `M = 36 = m₂`, `u = 4608`, `v = 7200`
(`4608·7200 = 16·1440²`, `(4608+7200)/2 = 5904 = 5·1440 − 36²`). -/
theorem conicform_pi3_instance_1440 :
    ∃ u v M : ℤ, u * v = 16 * (1440 : ℤ) ^ 2 ∧ (2 : ℤ) ∣ (u + v) ∧
      (u + v) / 2 = 5 * (1440 : ℤ) - M ^ 2 ∧ 0 < M ∧ M ^ 2 < 1440 ∧ (2 : ℤ) ∣ M - 1440 :=
  ⟨4608, 7200, 36, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

open Erdos634.Draft.G3CEqui135Control in
/-- 2π/3 half on the certified 1215-tiling: `conicform_2pi3_of_tiling_full` applies. -/
theorem conicform_2pi3_real_1215 :
    ∃ u v : ℤ, u * v = 16 * (1215 : ℤ) ^ 2 ∧ (2 : ℤ) ∣ (u + v) ∧
      ∃ s : ℤ, (u + v) / 2 - 5 * (1215 : ℤ) = s ^ 2 ∧ s ∣ 3 * (1215 : ℤ) ∧
        (2 : ℤ) ∣ s - 1215 ∧ (2 : ℤ) ∣ 3 * (1215 : ℤ) / s - 1215 := by
  have hS : ∀ k, D.target.oppLen k = 1890 * 135 := by
    intro k
    fin_cases k
    · exact t_opp0
    · exact t_opp1
    · exact t_opp2
  have h := conicform_2pi3_of_tiling_full D α_irr data
    ⟨5670, 9450, 13230, by norm_num, by norm_num, by norm_num⟩ t_angle hS
  have hN : (Erdos634.Draft.G3CEqui135.cert.leaves.length : ℤ) = 1215 := by
    exact_mod_cast Erdos634.Draft.G3CEqui135.cert_len
  rw [hN] at h
  exact h

end Erdos634.Draft.FDCConicFormPi3Wit

#print axioms Erdos634.Draft.FDCConicFormPi3Wit.sixty_values_1440
#print axioms Erdos634.Draft.FDCConicFormPi3Wit.conicform_pi3_real_1440
#print axioms Erdos634.Draft.FDCConicFormPi3Wit.conicform_pi3_instance_1440
#print axioms Erdos634.Draft.FDCConicFormPi3Wit.conicform_2pi3_real_1215
