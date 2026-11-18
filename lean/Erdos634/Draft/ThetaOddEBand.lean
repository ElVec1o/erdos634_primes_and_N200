-- Draft/ThetaOddEBand.lean -- ODD-E formalization, module 14: THEOREM B (band recipe) in Lean: `thetaTiled_band`.
-- INTERNAL BUILD ONLY, UNAUDITED beyond internal checks.  No sorry, no native_decide.
/-
**`thetaTiled_band`.**  For integers `1 <= e < f`, `n >= 1`, `M`, `k >= 1`, `s`, with `t = M + k`, `w = t - s`, `b = f^2 - e^2`, `g = f - e`:
 (a) `g n >= e`, `f n <= e M`;  (b') `e n f <= k b`;  (c) `e n <= w f`;  (d) `g (s - k) >= e` (and `k < s < t`);  `e | w`;
 `e (k b - e n f) = x (e f) + r b + m f^2` (`x, r, m : N`);  and `rho = e M - f floor(e M / f) >= 1` (i.e. `f` does not divide `e M`),
`theta_t(e,f)` (legs `t b f`, base `t b e`) is cut into `b t^2` copies of the tile `(e f, b, f^2)`.
Proof: the generalised notch `thetaTiled_notch4` (module `ThetaOddEMain`: L, U, strips, `(fn)tau`) plus the R group `rgHP` (Theorem B's P1-P8).
Extra hypotheses over the hand statement (findings): `rho >= 1` (not formalised: `rho = 0` is a different case of the notch), nothing else;
coprimality of `e, f` is NOT used (`e | w` gives `e | z = w f - e n` directly); `1 <= j` is not needed (`0 < k` only).
The notch construction is the project's (Bonfioli); the first instance `theta_13(3,4)` was found by computer search on 2026-11-15; Theorem B is the AI assistant's
(internal working notes S2), hand-audited in internal audit-11-15.  Credit: Paliy (band steps), Beeson (48-tile seed),
Laczkovich, Zhang, Beeson-Rosu (skew frame, cells).  INTERNAL BUILD ONLY, UNAUDITED beyond internal checks.
-/
import Erdos634.Draft.ThetaOddERG3

open scoped Classical
open Erdos634.Geometry Erdos634.CertCoord

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Erdos634.Draft.ThetaNotch
noncomputable section
open Erdos634.Draft.WFrameF Erdos634.Draft.RegionTiling Erdos634.Draft.WBrickF Erdos634.Draft.CollarLayer
open Erdos634.Draft.LadderFam Erdos634.Draft.CollarFam
open Erdos634.Draft.ThetaUnit (ThetaTiled)

def TFamWeaken {M : Erdos634.Geometry.Tri} {S S' : Set Plane} {n : ℕ} (R : TFam S M n) (h : S ⊆ S') : TFam S' M n :=
  { tile := R.tile, sub := fun i => (R.sub i).trans h, disj := R.disj, cong := R.cong }

set_option maxHeartbeats 16000000 in
theorem thetaTiled_band (e f n M k s x r m : ℕ) (he : 1 ≤ e) (hef : e < f) (hn : 1 ≤ n) (ha1 : e ≤ (f - e) * n)
    (ha2 : f * n ≤ e * M) (hk : 0 < k) (hks : k < s) (hst : s < M + k) (hd : e + (f - e) * k ≤ (f - e) * s)
    (hc : e * n + s * f ≤ (M + k) * f) (hw : e ∣ M + k - s)
    (hY : e * (k * (f * f - e * e)) = e * (e * n * f) + (x * (e * f) + r * (f * f - e * e) + m * (f * f)))
    (hrho : ¬ f ∣ e * M) : ThetaTiled e f (f * f - e * e) (M + k) := by
  have hee : e * e ≤ f * f := Nat.mul_self_le_mul_self hef.le
  obtain ⟨b, hbdef⟩ : ∃ b, b = f * f - e * e := ⟨_, rfl⟩
  have hb : f * f = e * e + b := by omega
  rw [← hbdef] at hY ⊢
  have hf0 : 0 < f := by omega
  have hB : e * n * f ≤ k * b := by
    have : e * (e * n * f) ≤ e * (k * b) := by rw [hY]; omega
    exact Nat.le_of_mul_le_mul_left this he
  obtain ⟨wq, hwq⟩ := hw
  have hn_wq : n ≤ wq * f := by
    have h1 : e * n ≤ (M + k - s) * f := by
      rw [Nat.sub_mul]; omega
    rw [hwq, mul_assoc] at h1
    exact Nat.le_of_mul_le_mul_left h1 he
  obtain ⟨cn, hcn⟩ : ∃ cn, cn + n = wq * f := ⟨wq * f - n, by omega⟩
  let P : NP4 :=
    { e := e, f := f, g := f - e, b := b, M := M, n := n, n1 := e * M / f, k := k, s := s, rho := e * M % f
      he := he, hg := by omega, hfg := by omega, hb := hb, hn := hn
      hnn := (Nat.le_div_iff_mul_le hf0).2 (by rw [mul_comm]; exact ha2)
      hgn := ha1, hrho := (Nat.div_add_mod (e * M) f).symm
      hr1 := Nat.pos_of_ne_zero (fun h => hrho (Nat.dvd_of_mod_eq_zero h))
      hrf := Nat.mod_lt _ hf0, hk := hk, hks := hks, hst := hst, hB := hB, hC := hc, hD := hd }
  have hsub1 : e * 1 ≤ e * n + x := by nlinarith
  obtain ⟨Rc, hRcdef⟩ : ∃ Rc : ℕ, Rc = 2 * (wq * b) * r + (0 + 2 * (f * n) * m + (e * n) * (e * n) + 2 * (e * n) * x) +
      cn * ((e * 1) * (e * 1) + 2 * (f * 1) * m + (e * 1) * (e * 1) + 2 * (e * 1) * (e * n + x - e * 1)) := ⟨_, rfl⟩
  have hRc : Rc + (e * n) * (e * n) = 2 * (M + k - s) * k * b := by
    rw [hRcdef, hwq]
    have hYZ := congrArg (Nat.cast : ℕ → ℤ) hY
    push_cast at hYZ
    have hcnZ : (cn : ℤ) = wq * f - n := by
      have := congrArg (Nat.cast : ℕ → ℤ) hcn
      push_cast at this; linarith
    zify [hsub1]
    rw [hcnZ]
    linear_combination (-2 * (wq : ℤ)) * hYZ
  refine thetaTiled_notch4 P Rc hRc ?_
  intro φ hφ hφE
  have hE : (0 : ℝ) < e := by exact_mod_cast he
  have hEF : (e : ℝ) < f := by exact_mod_cast hef
  have hF : (0 : ℝ) < f := by linarith
  have hbR : (b : ℝ) = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
    have := congrArg (Nat.cast : ℕ → ℝ) hb; push_cast at this; nlinarith
  set mu : ℝ := (m : ℝ) * f / e with hmu
  set ac : ℝ := (e : ℝ) * f / (f : ℝ) ^ 2 with hac
  set ca : ℝ := (f : ℝ) ^ 2 / ((e : ℝ) * f) with hca
  set ab : ℝ := (e : ℝ) * f / ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) with hab
  set ba : ℝ := ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) / ((e : ℝ) * f) with hba
  set V1 : ℝ := (e : ℝ) * n + x + mu with hV1
  set H : ℝ := ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) / f * (k : ℝ) with hHdef
  set p : ℝ := (e : ℝ) * n + (cn : ℝ) * e with hp
  have hYR : (e : ℝ) * (k * b) = e * (e * n * f) + (x * (e * f) + r * b + m * (f * f)) := by exact_mod_cast hY
  have hH : H = V1 + (r : ℝ) * ba := by
    rw [hHdef, hV1, hmu, hba]
    rw [hbR] at hYR
    field_simp
    linear_combination hYR
  have key := rgHP hφ e f he hef hφE (s : ℝ) (M : ℝ) (k : ℝ) b wq r n x m cn hbR hn hcn mu V1 H p ac ca ab ba hmu hac hca hab hba hV1 hH hp
  have hKj : (k : ℝ) = P.jR * f := P.jRf.symm
  have hpp : p = ((M : ℝ) + k - s) * f := by
    have h1 : ((M + k - s : ℕ) : ℝ) = (M : ℝ) + k - s := by rw [Nat.cast_sub hst.le]; push_cast; ring
    have h2 : ((M + k - s : ℕ) : ℝ) = e * wq := by rw [hwq]; push_cast; ring
    have hcnR : (cn : ℝ) + n = wq * f := by exact_mod_cast hcn
    have h3 : (M : ℝ) + k - s = e * wq := by rw [← h1, h2]
    rw [hp, h3]; linear_combination (e : ℝ) * hcnR
  have hmono : HexS (e : ℝ) f (s : ℝ) (M : ℝ) (k : ℝ) ⟨0, p, 0, H, ((e * n : ℕ) : ℝ), p + H⟩ ⊆
      HexS (e : ℝ) f (s : ℝ) (M : ℝ) (k : ℝ) ⟨0, p, 0, H, (e : ℝ) * n, p + H⟩ :=
    hexS_mono le_rfl le_rfl le_rfl le_rfl (by show (e : ℝ) * n ≤ ((e * n : ℕ) : ℝ); push_cast; exact le_refl _) le_rfl
  have hsub : key.1.S ⊆ rReg2 (e : ℝ) f M n P.jR s := by
    have h1 := key.1.h
    rw [key.2.1] at h1
    exact h1.trans (hmono.trans (hexS_sub_rReg2 hE hEF (s : ℝ) (M : ℝ) (k : ℝ) P.jR n p H (p + H) hKj hHdef hpp))
  exact castTF rfl (key.2.2.trans hRcdef.symm) (TFamWeaken key.1.T (Set.image_mono hsub))

end

end Erdos634.Draft.ThetaNotch
