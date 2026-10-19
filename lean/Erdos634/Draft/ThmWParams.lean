-- Draft/ThmWParams.lean — Theorem W, Lemma C of PROOF.md section 5: the canonical parameters t = n - [rho = 0], r = n + 1, q = n satisfy WP.
-- Real-arithmetic lemmas (cases rho > 0 and rho = 0), then the natural-number interface.  UNAUDITED.  No sorry.
import Erdos634.Draft.ThmWNat

namespace Erdos634.Draft.ThmW

/-- Case `rho >= 1`: `t = n`. -/
theorem canonA (e f M n ρ s : ℝ) (he : 2 ≤ e) (hg : 2 ≤ f - e) (hF4 : f + 1 ≤ e * (f - e)) (hn : 1 ≤ n)
    (hρ1 : 1 ≤ ρ) (hρf : ρ ≤ f - 1) (hE : e * M = f * n + ρ) (hMs : M = n + s) (hs : 2 ≤ s)
    (hF5 : e + 1 ≤ (f - e) * n) : WP e f M n (n + 1) n := by
  have hf : 0 < f := by linarith
  have he0 : 0 < e := by linarith
  have hgn : (f - e) * n = e * s - ρ := by rw [hMs] at hE; linarith
  have hgM : (f - e) * M = f * s - ρ := by rw [hMs]; nlinarith
  have hΨ : 0 < f ^ 3 + 2 * e * f ^ 2 - e ^ 2 * f - e ^ 3 := by nlinarith [mul_pos he0 hf, mul_pos (mul_pos he0 he0) hf, mul_pos (mul_pos hf hf) he0, mul_pos (mul_pos hf hf) hf, sq_nonneg (f - e), mul_pos he0 (by linarith : 0 < f - e)]
  have hκ : 0 < 2 * f ^ 2 - e ^ 2 := by nlinarith
  have hb : 0 < f ^ 2 - e ^ 2 := by nlinarith
  have LB : 0 < (f ^ 2 - e ^ 2) * f * M - e * (2 * f ^ 2 - e ^ 2) * (n + 1) + f ^ 3 * n := by
    have key : (f ^ 2 - e ^ 2) * f * M - e * (2 * f ^ 2 - e ^ 2) * (n + 1) + f ^ 3 * n
        = s * (f ^ 3 + 2 * e * f ^ 2 - e ^ 2 * f - e ^ 3) - (2 * f ^ 2 - e ^ 2) * (ρ + e) := by
      rw [hMs]; linear_combination (2 * f ^ 2 - e ^ 2) * hgn
    rw [key]
    nlinarith [mul_le_mul_of_nonneg_right hs hΨ.le, mul_pos hκ (by linarith : 0 < f - ρ), mul_pos hκ (by linarith : (0:ℝ) < f - e)]
  refine ⟨he0, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith, ?_, ?_, ?_, ?_, ?_, ?_, ?_, LB, ?_⟩
  · linarith
  · nlinarith
  · -- c5
    have key : f * (f * M - e * (n + 1)) = (f + e) * (f * s - ρ) + e * ρ - e * f := by
      rw [hMs] at hE ⊢; nlinarith
    have : 0 < f * (f * M - e * (n + 1)) := by
      rw [key]; nlinarith [mul_le_mul_of_nonneg_left (by nlinarith [mul_le_mul_of_nonneg_left hs hf.le] : f + 1 ≤ f * s - ρ) (by linarith : (0:ℝ) ≤ f + e)]
    exact pos_of_mul_pos_right this hf.le
  · nlinarith
  · nlinarith
  · nlinarith [mul_le_mul_of_nonneg_left hF5 (by linarith : (0:ℝ) ≤ f + e)]
  · -- la
    nlinarith [mul_pos hκ he0]
  · -- lc
    have key : e * f * (f ^ 2 - e ^ 2) * M - e ^ 2 * (2 * f ^ 2 - e ^ 2) * (n + 1) + f ^ 4 * n
        = e * f * (f + e) * (f * s - ρ) + (f ^ 2 - e ^ 2) ^ 2 * n - e ^ 2 * (2 * f ^ 2 - e ^ 2) := by
      linear_combination (e * f * (f + e)) * hgM
    rw [key]
    have h1 : f + 1 ≤ f * s - ρ := by nlinarith [mul_le_mul_of_nonneg_left hs hf.le]
    nlinarith [mul_le_mul_of_nonneg_left h1 (by positivity : (0:ℝ) ≤ e * f * (f + e)), mul_nonneg (sq_nonneg (f ^ 2 - e ^ 2)) (by linarith : (0:ℝ) ≤ n), mul_pos hf he0, mul_pos (mul_pos hf hf) (by linarith : (0:ℝ) < f - e), mul_pos (mul_pos he0 he0) he0]

/-- Case `rho = 0`: `M = f m`, `n = e m`, `t = n - 1`. -/
theorem canonB (e f m : ℝ) (he : 2 ≤ e) (hg : 2 ≤ f - e) (hF4 : f + 1 ≤ e * (f - e)) (hm : 1 ≤ m) :
    WP e f (f * m) (e * m - 1) (e * m + 1) (e * m) := by
  have hf : 0 < f := by linarith
  have he0 : 0 < e := by linarith
  have hκ : 0 < 2 * f ^ 2 - e ^ 2 := by nlinarith
  have hb : 0 < f ^ 2 - e ^ 2 := by nlinarith
  have hem : e ≤ e * m := by nlinarith
  have hgm : 2 ≤ (f - e) * m := by nlinarith
  have hF5 : f + 1 ≤ (f - e) * (e * m) := by nlinarith [mul_le_mul_of_nonneg_left hm (by nlinarith : (0:ℝ) ≤ e * (f - e))]
  have LB : 0 < (f ^ 2 - e ^ 2) * f * (f * m) - e * (2 * f ^ 2 - e ^ 2) * (e * m + 1) + f ^ 3 * (e * m) := by
    have P1 : e * (2 * f ^ 2 - e ^ 2) < f ^ 4 + e * f ^ 3 - 3 * e ^ 2 * f ^ 2 + e ^ 4 := by
      obtain ⟨g, hg2, rfl⟩ : ∃ g, 2 ≤ g ∧ f = e + g := ⟨f - e, hg, by ring⟩
      nlinarith [mul_pos he0 he0, pow_pos he0 3, pow_pos he0 4, mul_nonneg he0.le (by linarith : (0:ℝ) ≤ g), mul_nonneg (mul_nonneg he0.le he0.le) (by linarith : (0:ℝ) ≤ g),
        mul_nonneg (pow_nonneg he0.le 3) (by linarith : (0:ℝ) ≤ g), pow_nonneg (by linarith : (0:ℝ) ≤ g) 4, mul_nonneg he0.le (pow_nonneg (by linarith : (0:ℝ) ≤ g) 3),
        mul_nonneg (mul_nonneg he0.le he0.le) (pow_nonneg (by linarith : (0:ℝ) ≤ g) 2), mul_nonneg he0.le (pow_nonneg (by linarith : (0:ℝ) ≤ g) 2), mul_nonneg (mul_nonneg he0.le he0.le) (by linarith : (0:ℝ) ≤ g)]
    have key : (f ^ 2 - e ^ 2) * f * (f * m) - e * (2 * f ^ 2 - e ^ 2) * (e * m + 1) + f ^ 3 * (e * m)
        = m * (f ^ 4 + e * f ^ 3 - 3 * e ^ 2 * f ^ 2 + e ^ 4) - e * (2 * f ^ 2 - e ^ 2) := by ring
    rw [key]; nlinarith
  have hbe : f ^ 2 + e ^ 2 < e * (f ^ 2 - e ^ 2) := by
    nlinarith [mul_pos (by linarith : (0:ℝ) < f + e) (by linarith : (0:ℝ) < e * (f - e) - f), mul_pos he0 hf]
  have hbe' : f ^ 2 < e * (f ^ 2 - e ^ 2) - e ^ 2 := by nlinarith
  refine ⟨he0, by linarith, by positivity, by linarith, by linarith, by nlinarith, by nlinarith, ?_, ?_, ?_, ?_, ?_, ?_, ?_, LB, ?_⟩
  · nlinarith
  · nlinarith
  · nlinarith
  · nlinarith [mul_pos he0 (by linarith : (0:ℝ) < (f - e) * m - 1)]
  · nlinarith [mul_le_mul_of_nonneg_left hm (by nlinarith : (0:ℝ) ≤ e * (f - e))]
  · nlinarith [mul_le_mul_of_nonneg_left (by linarith : e ≤ e * m) hb.le]
  · nlinarith [mul_pos hκ he0]
  · -- lc
    have key : e * f * (f ^ 2 - e ^ 2) * (f * m) - e ^ 2 * (2 * f ^ 2 - e ^ 2) * (e * m + 1) + f ^ 4 * (e * m - 1)
        = m * (e * (f ^ 2 - e ^ 2) * (2 * f ^ 2 - e ^ 2)) - e ^ 2 * (2 * f ^ 2 - e ^ 2) - f ^ 4 := by ring
    rw [key]
    nlinarith [mul_le_mul_of_nonneg_right (le_refl m) (by positivity : 0 ≤ e * (f ^ 2 - e ^ 2) * (2 * f ^ 2 - e ^ 2)),
      mul_le_mul_of_nonneg_left hm (by positivity : (0:ℝ) ≤ e * (f ^ 2 - e ^ 2) * (2 * f ^ 2 - e ^ 2)),
      mul_pos hκ (by linarith : (0:ℝ) < e * (f ^ 2 - e ^ 2) - e ^ 2 - f ^ 2), mul_pos hf hf, mul_pos hκ hf]

end Erdos634.Draft.ThmW
