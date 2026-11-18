-- Draft/ThetaNotch2PU.lean -- STAGE 1b: apex data and half-plane facts of the U group pieces (v-tau, pi5, pi4, rho-tau, rho-par).
-- INTERNAL BUILD ONLY, UNAUDITED (reading audit 2026-11-14, SOUND WITH GAPS, internal audit).  No sorry, no native_decide.
/-
Credit: Paliy, Beeson, Laczkovich, Zhang, Beeson-Rosu; the project.  Pieces of `rust/audit_notch_20261114` (`t2_region`, rho > 0).
INTERNAL BUILD ONLY, UNAUDITED.
-/
import Erdos634.Draft.ThetaNotch2NP

open scoped Classical
open Erdos634.Geometry Erdos634.CertCoord

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Erdos634.Draft.ThetaNotch
noncomputable section
open Erdos634.Draft.WFrameF Erdos634.Draft.RegionTiling Erdos634.Draft.WBrickF Erdos634.Draft.CollarLayer
open Erdos634.Draft.LadderFam Erdos634.Draft.CollarFam
open Erdos634.Draft.S2L (baseTri tri_eq_of_pts)

def w2V1 (E F M n j : ℝ) : ℝ × ℝ := (vv E F M n / F, j * F)
def w2V2 (E F M n j : ℝ) : ℝ × ℝ := (0, j * F + F * vv E F M n / (F ^ 2 - E ^ 2))
def w2X5 (M n j F : ℝ) : ℝ × ℝ := (M - n, j * F)
def w2W (E F M n j : ℝ) : ℝ × ℝ := (M - E * n / F, j * F)
def w2U5 (E F M n j : ℝ) : ℝ × ℝ := (M - n, j * F + F * n / (E + F))
def w2Vt (F M j : ℝ) : ℝ × ℝ := (0, M + j * F)
def w2Qv (E F M n j : ℝ) : ℝ × ℝ := ((E * M - F * n) / E, M + j * F - (E * M - F * n) / E)
def w2Qp (E F M n j : ℝ) : ℝ × ℝ :=
  ((E * M - F * n) / E, M + j * F - (E * M - F * n) / E - E * (E * M - F * n) / (F ^ 2 - E ^ 2))
def w2Z (E F M n j : ℝ) : ℝ × ℝ := (M + E * n * (F / (F ^ 2 - E ^ 2)), j * F - E * n * (F / (F ^ 2 - E ^ 2)))
def w2Pp (M j F : ℝ) : ℝ × ℝ := (M, j * F)

def sig5b (E F n : ℝ) : ℝ := 1 - E / ((F - E) * n)

def vt2Reg (E F M n j s : ℝ) : Set (ℝ × ℝ) := Preg (cH E F s (uD F j)) (cH E F s (w2V1 E F M n j)) (cH E F s (w2V2 E F M n j)) 0
def p52Reg (E F M n j s : ℝ) : Set (ℝ × ℝ) :=
  Preg (cH E F s (w2X5 M n j F)) (cH E F s (w2W E F M n j)) (cH E F s (w2U5 E F M n j)) (sig5b E F n)
def p42Reg (E F M n j s : ℝ) : Set (ℝ × ℝ) := Par (cH E F s (w2Qv E F M n j)) (cHv E F (uw1 E F)) (cHv E F (uw2 E F)) F ((F - E) * n)
def rt2Reg (E F M n j s : ℝ) : Set (ℝ × ℝ) := Preg (cH E F s (w2Qv E F M n j)) (cH E F s (w2Qp E F M n j)) (cH E F s (w2Vt F M j)) 0
def rp2Reg (E F M n j s : ℝ) : Set (ℝ × ℝ) :=
  Par (cH E F s (w2Vt F M j)) (cHv E F (uw1 E F)) (cHv E F (uw2 E F)) (F - (E * M - F * n)) (E * M - F * n)

section U2
variable {E F M n j : ℝ} (s : ℝ) (H : RHU E F M n j)
include H

set_option maxHeartbeats 8000000 in
theorem vt2_facts :
    LF E F s (vt2Reg E F M n j s) (-1) 0 0 ∧ LF E F s (vt2Reg E F M n j s) 0 (-1) (-(j * F)) ∧
    LF E F s (vt2Reg E F M n j s) (F ^ 2) (F ^ 2 - E ^ 2) (c0f E F M n j) ∧
    LF E F s (vt2Reg E F M n j s) 1 1 (M + j * F) ∧
    LF E F s (vt2Reg E F M n j s) (F ^ 2) (F ^ 2 - E ^ 2) (laf E F M n j) := by
  obtain ⟨hF, hB, hEF', hn0, hM, hj0, hv, hen⟩ := H.pos
  have hE := H.hE
  have hEF := H.hEF
  have hr0 := H.hr0
  have hrF := H.hrF
  unfold vv at hv
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> unfold LF vt2Reg <;>
    refine preg_apex_le s hE hEF _ _ _ _ _ _ _ le_rfl zero_le_one ?_ ?_ ?_ ?_ <;>
    simp only [uD, w2V1, w2V2, vv, c0f, laf, zero_mul, add_zero] <;> field_simp <;>
    nlinarith [mul_pos hF hB, mul_pos hE hF, mul_pos hE hB, mul_pos hF hr0, mul_pos hF hv, mul_pos hB hv,
      mul_pos hE hv, mul_pos hE hr0, mul_pos hB hr0, mul_nonneg hB.le (sub_nonneg.2 hrF.le), mul_nonneg hF.le (sub_nonneg.2 hrF.le),
      mul_nonneg hE.le (sub_nonneg.2 hrF.le), mul_nonneg (mul_nonneg hF.le hB.le) (sub_nonneg.2 hrF.le), mul_pos hn0 hE]

set_option maxHeartbeats 8000000 in
theorem p52_facts :
    LF E F s (p52Reg E F M n j s) (-1) 0 (-(M - n)) ∧ LF E F s (p52Reg E F M n j s) 0 (-1) (-(j * F)) ∧
    LF E F s (p52Reg E F M n j s) (F ^ 2) (F ^ 2 - E ^ 2) (c0f E F M n j) ∧
    LF E F s (p52Reg E F M n j s) 1 1 (M + j * F) ∧
    LF E F s (p52Reg E F M n j s) (-(F ^ 2)) (-(F ^ 2 - E ^ 2)) (-(laf E F M n j)) := by
  obtain ⟨hF, hB, hEF', hn0, hM, hj0, hv, hen⟩ := H.pos
  have hE := H.hE
  have hEF := H.hEF
  have hr0 := H.hr0
  have hrF := H.hrF
  have hgn := H.hgn
  have hg : 0 < F - E := by linarith
  have hgnp : 0 < (F - E) * n := mul_pos hg hn0
  have hgne : F - E ≠ 0 := hg.ne'
  have hn0' : n ≠ 0 := hn0.ne'
  have hs0 : 0 ≤ sig5b E F n := by
    unfold sig5b; rw [sub_nonneg, div_le_one hgnp]; exact hgn
  have hs1 : sig5b E F n ≤ 1 := by
    unfold sig5b; have : 0 < E / ((F - E) * n) := by positivity
    linarith
  unfold vv at hv
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> unfold LF p52Reg <;>
    refine preg_apex_le s hE hEF _ _ _ _ _ _ _ hs0 hs1 ?_ ?_ ?_ ?_ <;>
    simp only [w2X5, w2W, w2U5, sig5b, vv, c0f, laf] <;> field_simp <;>
    nlinarith [mul_pos hF hB, mul_pos hE hF, mul_pos hE hB, mul_pos hF hr0, mul_pos hF hv, mul_pos hB hv,
      mul_pos hE hv, mul_pos hE hr0, mul_pos hB hr0, mul_nonneg hB.le (sub_nonneg.2 hrF.le), mul_nonneg hF.le (sub_nonneg.2 hrF.le),
      mul_nonneg hE.le (sub_nonneg.2 hrF.le), mul_nonneg (sub_nonneg.2 hgn) (mul_nonneg hE.le hg.le),
      mul_nonneg hF.le (mul_nonneg (sub_nonneg.2 hgn) hE.le), mul_nonneg hn0.le (mul_nonneg (sub_nonneg.2 hgn) hE.le), mul_pos hn0 hE]

set_option maxHeartbeats 8000000 in
theorem p42_facts :
    LF E F s (p42Reg E F M n j s) (-1) 0 (-((E * M - F * n) / E)) ∧ LF E F s (p42Reg E F M n j s) 1 0 (M - n) ∧
    LF E F s (p42Reg E F M n j s) 0 (-1) (-(j * F)) ∧
    LF E F s (p42Reg E F M n j s) (F ^ 2) (F ^ 2 - E ^ 2) (c0f E F M n j) ∧
    LF E F s (p42Reg E F M n j s) 1 1 (M + j * F) ∧
    LF E F s (p42Reg E F M n j s) (-(F ^ 2)) (-(F ^ 2 - E ^ 2)) (-(laf E F M n j)) := by
  obtain ⟨hF, hB, hEF', hn0, hM, hj0, hv, hen⟩ := H.pos
  have hE := H.hE
  have hEF := H.hEF
  have hr0 := H.hr0
  have hrF := H.hrF
  have hgn := H.hgn
  have hg : 0 < F - E := by linarith
  have hgnp : 0 < (F - E) * n := mul_pos hg hn0
  unfold vv at hv
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> unfold LF p42Reg <;>
    refine par_apex_le s hE hEF _ _ _ _ _ hF hgnp _ _ _ ?_ ?_ ?_ ?_ <;>
    simp only [w2Qv, uw1, uw2, vv, c0f, laf, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;>
    field_simp <;>
    nlinarith [mul_pos hF hB, mul_pos hE hF, mul_pos hE hB, mul_pos hF hr0, mul_pos hF hv, mul_pos hB hv,
      mul_pos hE hv, mul_pos hE hr0, mul_pos hB hr0, mul_nonneg hB.le (sub_nonneg.2 hrF.le), mul_nonneg hF.le (sub_nonneg.2 hrF.le),
      mul_nonneg hE.le (sub_nonneg.2 hrF.le), mul_nonneg (sub_nonneg.2 hgn) (mul_nonneg hE.le hg.le),
      mul_nonneg hF.le (mul_nonneg (sub_nonneg.2 hgn) hE.le), mul_nonneg hn0.le (mul_nonneg (sub_nonneg.2 hgn) hE.le), mul_pos hn0 hE]

set_option maxHeartbeats 8000000 in
theorem rt2_facts :
    LF E F s (rt2Reg E F M n j s) (-1) 0 0 ∧ LF E F s (rt2Reg E F M n j s) 1 0 ((E * M - F * n) / E) ∧
    LF E F s (rt2Reg E F M n j s) 0 (-1) (-(j * F)) ∧
    LF E F s (rt2Reg E F M n j s) (F ^ 2) (F ^ 2 - E ^ 2) (c0f E F M n j) ∧
    LF E F s (rt2Reg E F M n j s) 1 1 (M + j * F) ∧
    LF E F s (rt2Reg E F M n j s) (-(F ^ 2)) (-(F ^ 2 - E ^ 2)) (-(laf E F M n j)) ∧
    LF E F s (rt2Reg E F M n j s) (-(F ^ 2)) (-(F ^ 2 - E ^ 2)) (-((F ^ 2 - E ^ 2) * (M + j * F))) := by
  obtain ⟨hF, hB, hEF', hn0, hM, hj0, hv, hen⟩ := H.pos
  have hE := H.hE
  have hEF := H.hEF
  have hr0 := H.hr0
  have hrF := H.hrF
  have hgn := H.hgn
  unfold vv at hv
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> unfold LF rt2Reg <;>
    refine preg_apex_le s hE hEF _ _ _ _ _ _ _ le_rfl zero_le_one ?_ ?_ ?_ ?_ <;>
    simp only [w2Qv, w2Qp, w2Vt, vv, c0f, laf, zero_mul, add_zero] <;> field_simp <;>
    nlinarith [mul_pos hF hB, mul_pos hE hF, mul_pos hE hB, mul_pos hF hr0, mul_pos hF hv, mul_pos hB hv,
      mul_pos hE hv, mul_pos hE hr0, mul_pos hB hr0, mul_nonneg hB.le (sub_nonneg.2 hrF.le), mul_nonneg hF.le (sub_nonneg.2 hrF.le),
      mul_nonneg hE.le (sub_nonneg.2 hrF.le), mul_pos hn0 hE]

set_option maxHeartbeats 8000000 in
theorem rp2_facts :
    LF E F s (rp2Reg E F M n j s) (-1) 0 0 ∧ LF E F s (rp2Reg E F M n j s) 1 0 ((E * M - F * n) / E) ∧
    LF E F s (rp2Reg E F M n j s) 0 (-1) (-(j * F)) ∧
    LF E F s (rp2Reg E F M n j s) (F ^ 2) (F ^ 2 - E ^ 2) (c0f E F M n j) ∧
    LF E F s (rp2Reg E F M n j s) 1 1 (M + j * F) ∧
    LF E F s (rp2Reg E F M n j s) (-(F ^ 2)) (-(F ^ 2 - E ^ 2)) (-(laf E F M n j)) ∧
    LF E F s (rp2Reg E F M n j s) (F ^ 2) (F ^ 2 - E ^ 2) ((F ^ 2 - E ^ 2) * (M + j * F)) := by
  obtain ⟨hF, hB, hEF', hn0, hM, hj0, hv, hen⟩ := H.pos
  have hE := H.hE
  have hEF := H.hEF
  have hr0 := H.hr0
  have hrF := H.hrF
  have hgn := H.hgn
  have hp : 0 < F - (E * M - F * n) := by linarith
  unfold vv at hv
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> unfold LF rp2Reg <;>
    refine par_apex_le s hE hEF _ _ _ _ _ hp hr0 _ _ _ ?_ ?_ ?_ ?_ <;>
    simp only [w2Vt, uw1, uw2, vv, c0f, laf, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;>
    field_simp <;>
    nlinarith [mul_pos hF hB, mul_pos hE hF, mul_pos hE hB, mul_pos hF hr0, mul_pos hF hv, mul_pos hB hv,
      mul_pos hE hv, mul_pos hE hr0, mul_pos hB hr0, mul_nonneg hB.le (sub_nonneg.2 hrF.le), mul_nonneg hF.le (sub_nonneg.2 hrF.le),
      mul_nonneg hE.le (sub_nonneg.2 hrF.le), mul_pos hn0 hE, mul_pos hE hp, mul_pos hF hp, mul_pos hB hp]

end U2

end

end Erdos634.Draft.ThetaNotch
