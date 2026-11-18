-- Draft/ThetaNotchL.lean -- the L group of the notch seed: `k` unit theta strips (`ThetaUnit` pieces T, R) at the base vertex `(0,s)`.
-- INTERNAL BUILD ONLY, UNAUDITED.  No sorry, no native_decide.
/-
The skew frame of `ThetaUnit` at its base vertex `P` is exactly the frame `cH` of this development at `P = (0,s)`
(`X' = f b (s - x - y)`, `Y' = e b x`).  The strip over the old block `theta_n` is `T(n) u R(n)` (ladder trapezoids); it lies in the band
`e f b n <= e X' + f Y' <= e f b (n+1)`, i.e. `s - n - 1 <= y <= s - n`.  The `k` strips `n = s-k, ..., s-1` tile `L = {y <= k, x+y <= s}`.
Credit: Paliy (annulus/band steps on a seed), Beeson-Rosu (frame), the unit step `ThetaUnitStep` (this project, T1 of `internal notes`).
INTERNAL BUILD ONLY, UNAUDITED.
-/
import Erdos634.Draft.ThetaNotchFamR

open scoped Classical
open Erdos634.Geometry Erdos634.CertCoord

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Erdos634.Draft.ThetaNotch
noncomputable section
open Erdos634.Draft.WFrameF Erdos634.Draft.RegionTiling Erdos634.Draft.WBrickF Erdos634.Draft.CollarLayer
open Erdos634.Draft.LadderFam Erdos634.Draft.CollarFam
open Erdos634.Draft.ThetaUnit

/-- the band of the strip over `theta_n` -/
def bandReg (E F n : ℝ) : Set (ℝ × ℝ) :=
  {p | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ E * F * (F ^ 2 - E ^ 2) * n ≤ E * p.1 + F * p.2 ∧
    E * p.1 + F * p.2 ≤ E * F * (F ^ 2 - E ^ 2) * (n + 1)}

/-- **one strip**: `theta_{n+1} \ theta_n` at the base vertex, `b (2n+1)` tiles (the two ladder trapezoids of `ThetaUnit`) -/
def stripFam {φ : ℝ} (hφ : 1 < φ) (e f b n : ℕ) (he : 0 < e) (hef : e < f) (hb : f * f = e * e + b)
    (hφE : φ = (f : ℝ) / e) (hg : e ≤ (f - e) * n) :
    TFam (Phi φ '' bandReg (e : ℝ) f n) (Mrow hφ e f he hef) (((f + (f - e) * n) * (f + (f - e) * n) - ((f - e) * n) * ((f - e) * n)) +
      (((f - e) * n) * ((f - e) * n) - ((f - e) * n - e) * ((f - e) * n - e))) := by
  have hE : (0 : ℝ) < e := by exact_mod_cast he
  have hEF : (e : ℝ) < f := by exact_mod_cast hef
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hgR : (e : ℝ) ≤ ((f : ℝ) - e) * n := by
    have : ((e : ℕ) : ℝ) ≤ (((f - e) * n : ℕ) : ℝ) := by exact_mod_cast hg
    rwa [Nat.cast_mul, Nat.cast_sub hef.le] at this
  obtain ⟨hb0, ha0, hc0⟩ := pos_facts hE hEF
  have hF : (0 : ℝ) < f := by linarith
  set E : ℝ := (e : ℝ) with hEdef
  set F : ℝ := (f : ℝ) with hFdef
  set nR : ℝ := (n : ℝ) with hnRdef
  set M := Mrow hφ e f he hef with hMdef
  set g : ℕ := (f - e) * n with hgdef
  have hgcast : (g : ℝ) = gg E F nR := by
    rw [hgdef, Nat.cast_mul, Nat.cast_sub hef.le]; rfl
  have hegle : e ≤ g := hg
  have hglek : g ≤ f + g := Nat.le_add_left _ _
  have hkpos : 0 < f + g := by omega
  have hgpos : 0 < g := by omega
  have hkcast : ((f + g : ℕ) : ℝ) = F + gg E F nR := by push_cast; rw [hgcast]
  have hspcast : ((g - e : ℕ) : ℝ) = gg E F nR - E := by rw [Nat.cast_sub hegle, hgcast]
  have hσT : (g : ℝ) / ((f + g : ℕ) : ℝ) = gg E F nR / (F + gg E F nR) := by rw [hgcast, hkcast]
  have hσR : ((g - e : ℕ) : ℝ) / (g : ℝ) = (gg E F nR - E) / gg E F nR := by rw [hspcast, hgcast]
  let famT : TFam (Phi φ '' Preg (tY E F nR) (tO E F nR) (tU2 E F nR) ((g : ℝ) / ((f + g : ℕ) : ℝ))) M
      ((f + g) * (f + g) - g * g) :=
    ladderFam φ hφ (tY E F nR) (tO E F nR) (tU2 E F nR) (f + g) g hkpos hglek (det_T hE hEF hn hgR) M
      (cong_T hE hEF hn hgR hφ hφE hkpos hkcast hb0 ha0)
  let famR : TFam (Phi φ '' Preg (tAs E F nR) (tA2 E F nR) (tU1 E F nR) (((g - e : ℕ) : ℝ) / (g : ℝ))) M
      (g * g - (g - e) * (g - e)) :=
    ladderFam φ hφ (tAs E F nR) (tA2 E F nR) (tU1 E F nR) g (g - e) hgpos (Nat.sub_le g e) (det_R hE hEF hn hgR) M
      (cong_R hE hEF hn hgR hφ hφE hgpos hgcast hb0 ha0)
  have hTin := T_inTgt hE hEF hn hgR
  have hRin := R_inTgt hE hEF hn hgR
  have hTold := T_old hE hEF hn hgR
  have hRold := R_old hE hEF hn hgR
  have hTsep := T_sepR hE hEF hn hgR
  have hRsep := R_sepT hE hEF hn hgR
  rw [← hσT] at hTin hTold hTsep
  rw [← hσR] at hRin hRold hRsep
  have hE0 : E ≠ 0 := hE.ne'
  have hF0 : F ≠ 0 := hF.ne'
  refine TFam.join2 famT famR ?_ ?_ ?_
  · refine Set.image_mono (fun p hp => ?_)
    obtain ⟨a1, a2, a3⟩ := hTin p hp
    exact ⟨a2, a1, hTold p hp, by simpa [mul_assoc] using a3⟩
  · refine Set.image_mono (fun p hp => ?_)
    obtain ⟨a1, a2, a3⟩ := hRin p hp
    exact ⟨a2, a1, hRold p hp, by simpa [mul_assoc] using a3⟩
  · exact (disjoint_image hφ (interior_disj_lin F E (E * F * (F ^ 2 - E ^ 2) * nR) hF0 hRsep hTsep)).symm


/-- strip count: `(f+g)^2 - g^2 + g^2 - (g-e)^2 = b (2n+1)` for `g = (f-e) n >= e` -/
theorem strip_cnt (e f b n : ℕ) (hef : e < f) (hb : f * f = e * e + b) (hg : e ≤ (f - e) * n) :
    ((f + (f - e) * n) * (f + (f - e) * n) - ((f - e) * n) * ((f - e) * n)) +
      (((f - e) * n) * ((f - e) * n) - ((f - e) * n - e) * ((f - e) * n - e)) = b * (2 * n + 1) := by
  have h1 : (f - e) * n * ((f - e) * n) ≤ (f + (f - e) * n) * (f + (f - e) * n) :=
    Nat.mul_self_le_mul_self (Nat.le_add_left _ _)
  have h2 : ((f - e) * n - e) * ((f - e) * n - e) ≤ (f - e) * n * ((f - e) * n) :=
    Nat.mul_self_le_mul_self (Nat.sub_le _ _)
  apply Nat.cast_injective (R := ℤ)
  push_cast [Nat.cast_sub h1, Nat.cast_sub h2, Nat.cast_sub hg, Nat.cast_sub hef.le]
  have hbZ : (b : ℤ) = (f : ℤ) * f - (e : ℤ) * e := by
    have : ((f * f : ℕ) : ℤ) = ((e * e + b : ℕ) : ℤ) := by rw [hb]
    push_cast at this; linarith
  rw [hbZ]; ring

theorem ay_eq {E F : ℝ} (s : ℝ) (hE : 0 < E) (hEF : E < F) (p : ℝ × ℝ) :
    ay E F s p = s - (E * p.1 + F * p.2) / (E * F * (F ^ 2 - E ^ 2)) := by
  obtain ⟨hF, hb⟩ := frame_pos hE hEF
  simp only [ay]; field_simp; ring

def slReg (E F j s : ℝ) : Set (ℝ × ℝ) :=
  {p | (-1) * ax E F p + 0 * ay E F s p ≤ 0 ∧ 0 * ax E F p + (-1) * ay E F s p ≤ 0 ∧
    0 * ax E F p + 1 * ay E F s p ≤ j * F ∧ 1 * ax E F p + 1 * ay E F s p ≤ s}

theorem band_sub {E F : ℝ} (s n j : ℝ) (hE : 0 < E) (hEF : E < F) (hn1 : n + 1 ≤ s) (hn0 : s - j * F ≤ n) :
    bandReg E F n ⊆ slReg E F j s := by
  obtain ⟨hF, hb⟩ := frame_pos hE hEF
  have hEFB : 0 < E * F * (F ^ 2 - E ^ 2) := by positivity
  intro p ⟨h1, h2, h3, h4⟩
  have hay := ay_eq s hE hEF p
  have hx : 0 ≤ ax E F p := div_nonneg h2 (by positivity)
  have hq1 : n ≤ (E * p.1 + F * p.2) / (E * F * (F ^ 2 - E ^ 2)) := by rw [le_div_iff₀ hEFB]; linarith
  have hq2 : (E * p.1 + F * p.2) / (E * F * (F ^ 2 - E ^ 2)) ≤ n + 1 := by rw [div_le_iff₀ hEFB]; linarith
  have hy : ay E F s p = s - (E * p.1 + F * p.2) / (E * F * (F ^ 2 - E ^ 2)) := hay
  have hxy : ax E F p + ay E F s p = s - p.1 / (F * (F ^ 2 - E ^ 2)) := by
    simp only [ax, ay]; field_simp; ring
  have hp1 : 0 ≤ p.1 / (F * (F ^ 2 - E ^ 2)) := div_nonneg h1 (by positivity)
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

end

end Erdos634.Draft.ThetaNotch
