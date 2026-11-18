-- Draft/ThetaNotchPU.lean -- apex data and half-plane facts for the pieces of the U group (v-tau, pi5, pi4).
-- INTERNAL BUILD ONLY, UNAUDITED (reading audit 2026-11-14, SOUND WITH GAPS, internal audit).  No sorry, no native_decide.
/-
Credit: Paliy, Beeson, Laczkovich, Zhang, Beeson-Rosu; the project.  The pieces are those of `rust/audit_notch_20261114`
(`t2_region`, case rho = 0).  INTERNAL BUILD ONLY, UNAUDITED.
-/
import Erdos634.Draft.ThetaNotchGen

open scoped Classical
open Erdos634.Geometry Erdos634.CertCoord

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Erdos634.Draft.ThetaNotch
noncomputable section
open Erdos634.Draft.WFrameF Erdos634.Draft.RegionTiling Erdos634.Draft.WBrickF Erdos634.Draft.CollarLayer
open Erdos634.Draft.LadderFam Erdos634.Draft.CollarFam
open Erdos634.Draft.S2L (baseTri tri_eq_of_pts)

/-- the real-level hypotheses of the notch lemma (`rho = 0` case): `k = j F`, `M = F m`, `n = E m`, `t = F m + j F`.
`hB`: `e n <= j b`; `hC`: `e n <= (t - s) f`; `hD`: `e <= g (s - k)`; `hks`: `k < s`; `hst`: `s < t`. -/
structure RH (E F m j s : ℝ) : Prop where
  hE : 0 < E
  hEF : E < F
  hBE : E < F ^ 2 - E ^ 2
  hm : 1 ≤ m
  hj : 1 ≤ j
  hB : E * (E * m) < j * (F ^ 2 - E ^ 2)
  hC : E * (E * m) < (F * (m + j) - s) * F
  hD : E ≤ (F - E) * (s - j * F)
  hks : j * F < s
  hst : s < F * (m + j)
  hg1 : 1 ≤ F - E

/-! ### apex data (reals).  `k = j F`, `M = F m`, `n = E m`, `t = M + k`, `v = (F^2-E^2) m - E`, `gn = (F-E) E m`. -/
def uD (F j : ℝ) : ℝ × ℝ := (0, j * F)
def uV1 (E F m j : ℝ) : ℝ × ℝ := (((F ^ 2 - E ^ 2) * m - E) / F, j * F)
def uV2 (E F m j : ℝ) : ℝ × ℝ := (0, j * F + F * ((F ^ 2 - E ^ 2) * m - E) / (F ^ 2 - E ^ 2))
def uX5 (E F m j : ℝ) : ℝ × ℝ := ((F - E) * m, j * F)
def uW (E F m j : ℝ) : ℝ × ℝ := ((F ^ 2 - E ^ 2) * m / F, j * F)
def uU5 (E F m j : ℝ) : ℝ × ℝ := ((F - E) * m, j * F + F * E * m / (E + F))
def uVt (F m j : ℝ) : ℝ × ℝ := (0, F * m + j * F)
def uw1 (E F : ℝ) : ℝ × ℝ := (0, -E / (F ^ 2 - E ^ 2))
def uw2 (E F : ℝ) : ℝ × ℝ := (1 / E, -F ^ 2 / (E * (F ^ 2 - E ^ 2)))

def LF (E F s : ℝ) (S : Set (ℝ × ℝ)) (al be ga : ℝ) : Prop := ∀ p ∈ S, al * ax E F p + be * ay E F s p ≤ ga

def sig5 (E F m : ℝ) : ℝ := 1 - 1 / ((F - E) * m)
def vtReg (E F m j s : ℝ) : Set (ℝ × ℝ) := Preg (cH E F s (uD F j)) (cH E F s (uV1 E F m j)) (cH E F s (uV2 E F m j)) 0
def p5Reg (E F m j s : ℝ) : Set (ℝ × ℝ) := Preg (cH E F s (uX5 E F m j)) (cH E F s (uW E F m j)) (cH E F s (uU5 E F m j)) (sig5 E F m)
def p4Reg (E F m j s : ℝ) : Set (ℝ × ℝ) := Par (cH E F s (uVt F m j)) (cHv E F (uw1 E F)) (cHv E F (uw2 E F)) F ((F - E) * (E * m))

theorem RH.pos {E F m j s : ℝ} (H : RH E F m j s) :
    0 < F ∧ 0 < F ^ 2 - E ^ 2 ∧ 0 < E + F ∧ 0 < (F ^ 2 - E ^ 2) * m - E ∧ 0 ≤ m ∧ 0 ≤ j := by
  obtain ⟨hE, hEF, hBE, hm, hj, -⟩ := H
  have hF : 0 < F := by linarith
  have hB : 0 < F ^ 2 - E ^ 2 := by linarith
  refine ⟨hF, hB, by linarith, by nlinarith, by linarith, by linarith⟩

theorem RH.gm {E F m j s : ℝ} (H : RH E F m j s) : 1 ≤ (F - E) * m := by nlinarith [H.hg1, H.hm]

section U
variable {E F m j s : ℝ} (H : RH E F m j s)
include H

/-- v-tau: `x ≥ 0`, `y ≥ k`, `F² x + B y ≤ B t`, `F² x + B y ≤ B k + F v` -/
theorem vt_facts :
    LF E F s (vtReg E F m j s) (-1) 0 0 ∧ LF E F s (vtReg E F m j s) 0 (-1) (-(j * F)) ∧
    LF E F s (vtReg E F m j s) (F ^ 2) (F ^ 2 - E ^ 2) ((F ^ 2 - E ^ 2) * (F * m + j * F)) ∧
    LF E F s (vtReg E F m j s) (F ^ 2) (F ^ 2 - E ^ 2) ((F ^ 2 - E ^ 2) * (j * F) + F * ((F ^ 2 - E ^ 2) * m - E)) := by
  obtain ⟨hF, hB, hEF', hv, hm0, hj0⟩ := H.pos
  have hE := H.hE
  have hEF := H.hEF
  refine ⟨?_, ?_, ?_, ?_⟩ <;> unfold LF vtReg <;>
    refine preg_apex_le s hE hEF _ _ _ _ _ _ _ le_rfl zero_le_one ?_ ?_ ?_ ?_ <;>
    simp only [uD, uV1, uV2, zero_mul, add_zero] <;> field_simp <;> nlinarith [mul_nonneg hm0 hj0]

/-- pi5: `x ≥ 0`, `y ≥ k`, `F² x + B y ≤ B t`, `F² x + B y ≥ B k + F v`, `x ≥ (F-E) m` -/
theorem p5_facts :
    LF E F s (p5Reg E F m j s) (-1) 0 0 ∧ LF E F s (p5Reg E F m j s) 0 (-1) (-(j * F)) ∧
    LF E F s (p5Reg E F m j s) (F ^ 2) (F ^ 2 - E ^ 2) ((F ^ 2 - E ^ 2) * (F * m + j * F)) ∧
    LF E F s (p5Reg E F m j s) (-(F ^ 2)) (-(F ^ 2 - E ^ 2)) (-((F ^ 2 - E ^ 2) * (j * F) + F * ((F ^ 2 - E ^ 2) * m - E))) ∧
    LF E F s (p5Reg E F m j s) (-1) 0 (-((F - E) * m)) := by
  obtain ⟨hF, hB, hEF', hv, hm0, hj0⟩ := H.pos
  have hE := H.hE
  have hEF := H.hEF
  have hgm := H.gm
  have hg : 0 < F - E := by linarith
  have hgmp : 0 < (F - E) * m := by linarith
  have hmne : m ≠ 0 := (by linarith [H.hm] : (0 : ℝ) < m).ne'
  have hgne : F - E ≠ 0 := hg.ne'
  have hs0 : 0 ≤ sig5 E F m := by
    unfold sig5; rw [sub_nonneg, div_le_one hgmp]; exact hgm
  have hs1 : sig5 E F m ≤ 1 := by
    unfold sig5; have : 0 < 1 / ((F - E) * m) := by positivity
    linarith
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> unfold LF p5Reg <;>
    refine preg_apex_le s hE hEF _ _ _ _ _ _ _ hs0 hs1 ?_ ?_ ?_ ?_ <;>
    simp only [uX5, uW, uU5, sig5] <;> field_simp <;>
    nlinarith [mul_nonneg hm0 hj0, mul_nonneg (sub_nonneg.2 hgm) (mul_nonneg hE.le hg.le),
      mul_nonneg hF.le (mul_nonneg (sub_nonneg.2 hgm) (mul_nonneg hE.le hm0)),
      mul_nonneg hm0 (mul_nonneg (sub_nonneg.2 hgm) (mul_nonneg hE.le hg.le))]


/-- pi4: `x ≥ 0`, `y ≥ k`, `F² x + B y ≤ B t`, `F² x + B y ≥ B k + F v`, `x ≤ (F-E) m` -/
theorem p4_facts :
    LF E F s (p4Reg E F m j s) (-1) 0 0 ∧ LF E F s (p4Reg E F m j s) 0 (-1) (-(j * F)) ∧
    LF E F s (p4Reg E F m j s) (F ^ 2) (F ^ 2 - E ^ 2) ((F ^ 2 - E ^ 2) * (F * m + j * F)) ∧
    LF E F s (p4Reg E F m j s) (-(F ^ 2)) (-(F ^ 2 - E ^ 2)) (-((F ^ 2 - E ^ 2) * (j * F) + F * ((F ^ 2 - E ^ 2) * m - E))) ∧
    LF E F s (p4Reg E F m j s) 1 0 ((F - E) * m) := by
  obtain ⟨hF, hB, hEF', hv, hm0, hj0⟩ := H.pos
  have hE := H.hE
  have hEF := H.hEF
  have hgm := H.gm
  have hg : 0 < F - E := by linarith
  have hgmp : 0 < (F - E) * (E * m) := by
    have := H.hm; positivity
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> unfold LF p4Reg <;>
    refine par_apex_le s H.hE H.hEF _ _ _ _ _ hF hgmp _ _ _ ?_ ?_ ?_ ?_ <;>
    simp only [uVt, uw1, uw2, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;>
    field_simp <;>
    nlinarith [mul_nonneg hm0 hj0, mul_nonneg (sub_nonneg.2 hgm) (mul_nonneg hE.le hg.le),
      mul_nonneg hF.le (mul_nonneg (sub_nonneg.2 hgm) (mul_nonneg hE.le hm0)),
      mul_nonneg hm0 (mul_nonneg (sub_nonneg.2 hgm) (mul_nonneg hE.le hg.le))]

end U

end

end Erdos634.Draft.ThetaNotch
