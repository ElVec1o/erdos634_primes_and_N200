import Erdos634.BaseBetaTargetCoord

/-!
# The identities of the ladder lemma with the real angles

Clause (i) of the ladder lemma cites two identities,
`sin β = b√D/(2f³)` with `D = 4f² − 1` and `f·u_x + b·|cos 2γ| = c`, which were in Lean only in
integer form cleared of denominators (`OrderForcing.sinb_ident`, `OrderForcing.descent_ident`).
Here they are for the real angles `β = modelBeta 1 f`, `α = modelAlpha 1 f`, `γ = π − α − β` of the
tile `(f, f² − 1, f²)` (`BaseBetaTargetCoord`), for real `f > 1`:

* `sin_beta`     : `sin β = (f² − 1)·√(4f² − 1) / (2f³)`;
* `cos_two_gamma`: `cos 2γ = −cos α = −(2f² − 1)/(2f²)`  (`2γ = π + α`);
* `descent`      : `f·cos β + (f² − 1)·|cos 2γ| = f²`, i.e. `a cos β + b cos α = c`.

Clause (iii) cites `OrderForcing.ladder_no_base` for its last step.  The whole arithmetic statement
is `no_base_exit`: for `f ≥ 2`, an integer `n` and `K ≡ i (mod f)` with `0 < i < f`, the number
`f³·n − K·(f⁴ − 3f² + 1)` is not divisible by `f²`.

No statement here is about a tiling.  Standard axioms, no `sorry`.
-/

namespace Erdos634.Draft.LadderIdent

open Erdos634 Erdos634.BaseBetaTargetCoord

/-- `sin β = (f² − 1)·√(4f² − 1) / (2f³)`. -/
theorem sin_beta {f : ℝ} (hf : 1 < f) :
    Real.sin (modelBeta 1 f) = (f ^ 2 - 1) * Real.sqrt (4 * f ^ 2 - 1) / (2 * f ^ 3) := by
  have h0 : (0:ℝ) < 1 := one_pos
  have hf0 : (0:ℝ) < f := by linarith
  obtain ⟨hb0, hb2⟩ := modelBeta_mem h0 hf
  have hcos := cos_modelBeta h0 hf
  have hsinpos : 0 < Real.sin (modelBeta 1 f) :=
    Real.sin_pos_of_pos_of_lt_pi hb0 (by linarith [Real.pi_pos])
  have hD : (0:ℝ) < 4 * f ^ 2 - 1 := by nlinarith
  have hs : Real.sqrt (4 * f ^ 2 - 1) ^ 2 = 4 * f ^ 2 - 1 := Real.sq_sqrt hD.le
  have hb : (0:ℝ) < f ^ 2 - 1 := by nlinarith
  have hrhs : 0 < (f ^ 2 - 1) * Real.sqrt (4 * f ^ 2 - 1) / (2 * f ^ 3) := by
    have := Real.sqrt_pos.mpr hD
    positivity
  have hsq : Real.sin (modelBeta 1 f) ^ 2
      = ((f ^ 2 - 1) * Real.sqrt (4 * f ^ 2 - 1) / (2 * f ^ 3)) ^ 2 := by
    have h1 : Real.sin (modelBeta 1 f) ^ 2 = 1 - Real.cos (modelBeta 1 f) ^ 2 := by
      have := Real.sin_sq_add_cos_sq (modelBeta 1 f); linarith
    have hr : ((f ^ 2 - 1) * Real.sqrt (4 * f ^ 2 - 1) / (2 * f ^ 3)) ^ 2
        = (f ^ 2 - 1) ^ 2 * (4 * f ^ 2 - 1) / (2 * f ^ 3) ^ 2 := by
      rw [div_pow, mul_pow, hs]
    rw [h1, hcos, hr]
    unfold baseLen Nq
    field_simp
    ring
  nlinarith [hsq, hsinpos, hrhs,
    sq_nonneg (Real.sin (modelBeta 1 f) - (f ^ 2 - 1) * Real.sqrt (4 * f ^ 2 - 1) / (2 * f ^ 3))]

/-- `cos 2γ = −cos α = −(2f² − 1)/(2f²)`, with `γ = π − α − β`. -/
theorem cos_two_gamma {f : ℝ} (hf : 1 < f) :
    Real.cos (2 * (Real.pi - modelAlpha 1 f - modelBeta 1 f)) = -((2 * f ^ 2 - 1) / (2 * f ^ 2)) := by
  have hrel := modelAngle_rel 1 f
  have h2 : 2 * (Real.pi - modelAlpha 1 f - modelBeta 1 f) = modelAlpha 1 f + Real.pi := by
    linarith
  rw [h2, Real.cos_add_pi, cos_modelAlpha one_pos hf]
  norm_num

/-- **The descent identity**: `f·cos β + (f² − 1)·|cos 2γ| = f²`. -/
theorem descent {f : ℝ} (hf : 1 < f) :
    f * Real.cos (modelBeta 1 f)
      + (f ^ 2 - 1) * |Real.cos (2 * (Real.pi - modelAlpha 1 f - modelBeta 1 f))| = f ^ 2 := by
  have hf0 : (0:ℝ) < f := by linarith
  have hpos : (0:ℝ) < (2 * f ^ 2 - 1) / (2 * f ^ 2) := by
    have : (0:ℝ) < 2 * f ^ 2 - 1 := by nlinarith
    positivity
  rw [cos_two_gamma hf, abs_neg, abs_of_pos hpos, cos_modelBeta one_pos hf]
  unfold baseLen Nq
  field_simp
  ring

/-- **No base exit** (clause (iii)): the number `f³·n − K·(f⁴ − 3f² + 1)` is not divisible by `f²`
when `K ≡ i (mod f)` with `0 < i < f`. -/
theorem no_base_exit (f n K j i : ℤ) (hf : 2 ≤ f) (hK : K = (j - 1) * f + i) (hi0 : 0 < i)
    (hif : i < f) : ¬ (f ^ 2 ∣ f ^ 3 * n - K * (f ^ 4 - 3 * f ^ 2 + 1)) := by
  rintro ⟨t, ht⟩
  -- then `f ∣ K`
  have hfK : f ∣ K := ⟨f ^ 2 * n - K * (f ^ 3 - 3 * f) - f * t, by linear_combination (-1 : ℤ) * ht⟩
  have hfi : f ∣ i := by
    have : f ∣ K - (j - 1) * f := dvd_sub hfK (dvd_mul_left f _)
    have h2 : K - (j - 1) * f = i := by rw [hK]; ring
    rwa [h2] at this
  have := Int.le_of_dvd hi0 hfi
  omega

/-- Instance of the hypotheses: `f = 3`, `j = 1`, `i = 1`, `n = 2`. -/
example : ¬ ((3:ℤ) ^ 2 ∣ 3 ^ 3 * 2 - 1 * (3 ^ 4 - 3 * 3 ^ 2 + 1)) :=
  no_base_exit 3 2 1 1 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end Erdos634.Draft.LadderIdent
