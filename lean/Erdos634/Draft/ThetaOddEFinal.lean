-- Draft/ThetaOddEFinal.lean -- ODD-E formalization, module 15: `thetaTiled_oddE`, the instances, witnesses and negative controls.
-- INTERNAL BUILD ONLY, UNAUDITED beyond internal checks.  No sorry, no native_decide.
/-
**`thetaTiled_oddE`.**  For every odd `e >= 3` and every `t >= (e^2 + 5 e + 2)/2`, `theta_t(e, e+1)` (legs `t (2e+1)(e+1)`, base `t (2e+1) e`) is cut into
`(2e+1) t^2` copies of the tile `(e(e+1), 2e+1, (e+1)^2)`: `ThetaTiled e (e+1) (2*e+1) t`.  The seed `t1 = (e^2+5e+2)/2` is the case
`n = e, M = 2e, k = (e^2+e+2)/2, s = k + e, x = 0, r = (e-1)/2, m = (e+1)/2` of `ThetaNotch.thetaTiled_band` (Theorem B); every `t >= t1` by `thetaTiled_upset`.
The first instance `theta_13(3,4)` (1183 tiles) was found by computer search on 2026-11-15 (this project); the notch construction is the project's (Bonfioli);
Theorem B is the AI assistant's (internal working notes S2) and the odd-e family proof is internal working notes
Credit: Paliy (band steps on a seed), Beeson (48-tile seed), Laczkovich, Zhang, Beeson-Rosu (skew frame, lattice cells).
INTERNAL BUILD ONLY, UNAUDITED beyond internal checks.
-/
import Erdos634.Draft.ThetaOddEBand
import Erdos634.Draft.ThetaUnitUp

open scoped Classical
open Erdos634.Geometry

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Erdos634.Draft.ThetaOddE
noncomputable section
open Erdos634.Draft.ThetaUnit (ThetaTiled thetaTiled_upset)
open Erdos634.Draft.ThetaNotch (thetaTiled_band)
open Erdos634.Draft.TileCountFamilies (TileCount)

/-- the seed: `e = 2d+1`, `t1 = 2 d^2 + 7 d + 4 = (e^2+5e+2)/2` -/
theorem seed (d : ℕ) (hd : 1 ≤ d) : ThetaTiled (2 * d + 1) (2 * d + 2) (4 * d + 3) (2 * d ^ 2 + 7 * d + 4) := by
  have hg : 2 * d + 2 - (2 * d + 1) = 1 := by omega
  have hb : (2 * d + 2) * (2 * d + 2) - (2 * d + 1) * (2 * d + 1) = 4 * d + 3 := by
    apply Nat.sub_eq_of_eq_add; ring
  have ht : 4 * d + 2 + (2 * d ^ 2 + 3 * d + 2) = 2 * d ^ 2 + 7 * d + 4 := by ring
  have hw : 4 * d + 2 + (2 * d ^ 2 + 3 * d + 2) - (2 * d ^ 2 + 5 * d + 3) = 2 * d + 1 := by omega
  have h := thetaTiled_band (2 * d + 1) (2 * d + 2) (2 * d + 1) (4 * d + 2) (2 * d ^ 2 + 3 * d + 2) (2 * d ^ 2 + 5 * d + 3) 0 d (d + 1)
    (by omega) (by omega) (by omega) (by rw [hg]; omega) (by nlinarith) (by positivity) (by nlinarith) (by nlinarith)
    (by rw [hg]; nlinarith) (by nlinarith) (by rw [hw])
    (by rw [hb]; ring)
    (by
      rintro ⟨q, hq⟩
      have h2 : (2 * d + 2) ∣ 2 := by
        have h3 : (2 * d + 2) ∣ (2 * d + 2) * (4 * d) + 2 := ⟨q, by rw [← hq]; ring⟩
        exact (Nat.dvd_add_right (Dvd.intro (4 * d) rfl)).1 h3
      have := Nat.le_of_dvd (by norm_num) h2
      omega)
  rw [hb, ht] at h
  exact h

/-- the unit step from the seed gives every `t >= t1`. -/
theorem thetaTiled_oddE (e : ℕ) (he : 3 ≤ e) (hodd : Odd e) (t : ℕ) (ht : (e ^ 2 + 5 * e + 2) / 2 ≤ t) :
    ThetaTiled e (e + 1) (2 * e + 1) t := by
  obtain ⟨d, rfl⟩ := hodd
  have hd : 1 ≤ d := by omega
  have hs := seed d hd
  have h1 : ((2 * d + 1) ^ 2 + 5 * (2 * d + 1) + 2) / 2 = 2 * d ^ 2 + 7 * d + 4 := by
    rw [show (2 * d + 1) ^ 2 + 5 * (2 * d + 1) + 2 = 2 * (2 * d ^ 2 + 7 * d + 4) by ring]
    exact Nat.mul_div_cancel_left _ (by norm_num)
  rw [h1] at ht
  have e1 : 2 * d + 1 + 1 = 2 * d + 2 := by ring
  have e2 : 2 * (2 * d + 1) + 1 = 4 * d + 3 := by ring
  rw [e1, e2]
  refine thetaTiled_upset (2 * d + 1) (2 * d + 2) (4 * d + 3) (2 * d ^ 2 + 7 * d + 4) (by omega) (by omega)
    (by ring) ?_ hs t ht
  have hg : 2 * d + 2 - (2 * d + 1) = 1 := by omega
  rw [hg]; nlinarith

/-- **corollary: tile counts** -/
theorem tileCount_oddE (e : ℕ) (he : 3 ≤ e) (hodd : Odd e) (t : ℕ) (ht : (e ^ 2 + 5 * e + 2) / 2 ≤ t) :
    TileCount ((2 * e + 1) * t * t) := by
  obtain ⟨D, -, -⟩ := thetaTiled_oddE e he hodd t ht
  exact ⟨D⟩

/-- the first instance, `theta_13(3,4)`: 1183 tiles of `(12, 7, 16)` -/
theorem thetaTiled_3_4_13 : ThetaTiled 3 4 7 13 := thetaTiled_oddE 3 le_rfl ⟨1, by norm_num⟩ 13 (by norm_num)
theorem tileCount_1183 : TileCount 1183 := by
  have := tileCount_oddE 3 le_rfl ⟨1, by norm_num⟩ 13 (by norm_num); simpa using this
theorem tileCount_77824 : TileCount 77824 := by
  have := tileCount_oddE 9 (by norm_num) ⟨4, by norm_num⟩ 64 (by norm_num); simpa using this
theorem tileCount_80275 : TileCount 80275 := by
  have := tileCount_oddE 9 (by norm_num) ⟨4, by norm_num⟩ 65 (by norm_num); simpa using this
theorem tileCount_85291 : TileCount 85291 := by
  have := tileCount_oddE 9 (by norm_num) ⟨4, by norm_num⟩ 67 (by norm_num); simpa using this

/-! ### Theorem B instances outside the odd-e family -/

/-- `theta_6(2,5)`: `(n, M, k, s, x, r, m) = (1, 3, 3, 4, 6, 1, 1)`, `Y = 106 = 6 a + b + c` -/
theorem thetaTiled_2_5_6 : ThetaTiled 2 5 21 6 :=
  thetaTiled_band 2 5 1 3 3 4 6 1 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
/-- `theta_7(3,8)`: `(n, M, k, s, x, r, m) = (1, 4, 3, 4, 2, 1, 5)` -/
theorem thetaTiled_3_8_7 : ThetaTiled 3 8 55 7 :=
  thetaTiled_band 3 8 1 4 3 4 2 1 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
theorem tileCount_2695 : TileCount 2695 := by
  obtain ⟨D, -, -⟩ := thetaTiled_3_8_7; exact ⟨D⟩
theorem tileCount_756 : TileCount 756 := by
  obtain ⟨D, -, -⟩ := thetaTiled_2_5_6; exact ⟨D⟩

/-! ### controls -/

/-- **witness**: the hypotheses of `thetaTiled_band` are satisfiable (at `theta_13(3,4)`: the seed `d = 1`). -/
theorem band_hyps_witness :
    ∃ (e f n M k s x r m : ℕ), 1 ≤ e ∧ e < f ∧ 1 ≤ n ∧ e ≤ (f - e) * n ∧ f * n ≤ e * M ∧ 0 < k ∧ k < s ∧ s < M + k ∧
      e + (f - e) * k ≤ (f - e) * s ∧ e * n + s * f ≤ (M + k) * f ∧ e ∣ M + k - s ∧
      e * (k * (f * f - e * e)) = e * (e * n * f) + (x * (e * f) + r * (f * f - e * e) + m * (f * f)) ∧ ¬ f ∣ e * M ∧
      M + k = 13 ∧ e = 3 ∧ f = 4 :=
  ⟨3, 4, 3, 6, 7, 10, 0, 1, 2, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, rfl, rfl⟩

/-- **negative control (2,3)**: the hypotheses of `thetaTiled_band` cannot hold at `(e,f) = (2,3)` with `t = M + k <= 6`
(the engine NO of `ThetaKill`: `theta_t(2,3)` is untiled for `t <= 4`, and the thick bound `t >= f + 2`). -/
theorem band_hyps_not_2_3 (n M k s x r m : ℕ) (hn : 1 ≤ n) (ha1 : 2 ≤ (3 - 2) * n) (ha2 : 3 * n ≤ 2 * M) (hk : 0 < k) (hks : k < s)
    (hst : s < M + k) (hd : 2 + (3 - 2) * k ≤ (3 - 2) * s) (hc : 2 * n + s * 3 ≤ (M + k) * 3) (hw : 2 ∣ M + k - s)
    (hY : 2 * (k * (3 * 3 - 2 * 2)) = 2 * (2 * n * 3) + (x * (2 * 3) + r * (3 * 3 - 2 * 2) + m * (3 * 3)))
    (hrho : ¬ 3 ∣ 2 * M) : 7 ≤ M + k := by
  omega

/-- **negative control (1,f)**: at `e = 1`, `f = 3, 4` the hypotheses force `t >= 2 f` (consistent with `thetaTiled_e1_iff`: `theta_t(1,f)` is tiled iff `t >= 2f`). -/
theorem band_hyps_e1_f3 (n M k s x r m : ℕ) (hn : 1 ≤ n) (ha1 : 1 ≤ (3 - 1) * n) (ha2 : 3 * n ≤ 1 * M) (hk : 0 < k) (hks : k < s)
    (hst : s < M + k) (hd : 1 + (3 - 1) * k ≤ (3 - 1) * s) (hc : 1 * n + s * 3 ≤ (M + k) * 3) (hw : 1 ∣ M + k - s)
    (hY : 1 * (k * (3 * 3 - 1 * 1)) = 1 * (1 * n * 3) + (x * (1 * 3) + r * (3 * 3 - 1 * 1) + m * (3 * 3)))
    (hrho : ¬ 3 ∣ 1 * M) : 6 ≤ M + k := by
  omega

theorem band_hyps_e1_f4 (n M k s x r m : ℕ) (hn : 1 ≤ n) (ha1 : 1 ≤ (4 - 1) * n) (ha2 : 4 * n ≤ 1 * M) (hk : 0 < k) (hks : k < s)
    (hst : s < M + k) (hd : 1 + (4 - 1) * k ≤ (4 - 1) * s) (hc : 1 * n + s * 4 ≤ (M + k) * 4) (hw : 1 ∣ M + k - s)
    (hY : 1 * (k * (4 * 4 - 1 * 1)) = 1 * (1 * n * 4) + (x * (1 * 4) + r * (4 * 4 - 1 * 1) + m * (4 * 4)))
    (hrho : ¬ 4 ∣ 1 * M) : 8 ≤ M + k := by
  omega

end

end Erdos634.Draft.ThetaOddE

#print axioms Erdos634.Draft.ThetaNotch.thetaTiled_band
#print axioms Erdos634.Draft.ThetaOddE.thetaTiled_oddE
#print axioms Erdos634.Draft.ThetaOddE.tileCount_oddE
#print axioms Erdos634.Draft.ThetaOddE.thetaTiled_3_4_13
#print axioms Erdos634.Draft.ThetaOddE.tileCount_77824
#print axioms Erdos634.Draft.ThetaOddE.tileCount_80275
#print axioms Erdos634.Draft.ThetaOddE.tileCount_85291
#print axioms Erdos634.Draft.ThetaOddE.tileCount_2695
#print axioms Erdos634.Draft.ThetaOddE.thetaTiled_2_5_6
#print axioms Erdos634.Draft.ThetaOddE.band_hyps_witness
#print axioms Erdos634.Draft.ThetaOddE.band_hyps_not_2_3
