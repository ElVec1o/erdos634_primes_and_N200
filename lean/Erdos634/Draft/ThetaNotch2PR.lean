-- Draft/ThetaNotch2PR.lean -- STAGE 1b: apex data and half-plane facts of the Rh group (C1, C2, C3) and the notch triangle, general (M, n).
-- INTERNAL BUILD ONLY, UNAUDITED (reading audit 2026-11-14, SOUND WITH GAPS, internal audit).  No sorry, no native_decide.
/-
Credit: Paliy, Beeson, Laczkovich, Zhang, Beeson-Rosu; the project.  Same pieces as `ThetaNotchPR` with the corner `P = (M,k)` and the
notch size `n` independent (`M = F m`, `n = E m` only in the case rho = 0).  `Rh = P + [0,p] r1 + [0,q] r2`, `p = (t-s) F`, `q = j B`.
INTERNAL BUILD ONLY, UNAUDITED.
-/
import Erdos634.Draft.ThetaNotch2PU

open scoped Classical
open Erdos634.Geometry Erdos634.CertCoord

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Erdos634.Draft.ThetaNotch
noncomputable section
open Erdos634.Draft.WFrameF Erdos634.Draft.RegionTiling Erdos634.Draft.WBrickF Erdos634.Draft.CollarLayer
open Erdos634.Draft.LadderFam Erdos634.Draft.CollarFam
open Erdos634.Draft.S2L (baseTri tri_eq_of_pts)

def pR2 (F M j s : ℝ) : ℝ := (M + j * F - s) * F
def w2C3 (E F M n j : ℝ) : ℝ × ℝ :=
  (M - E * n / F + E * n * (F / (F ^ 2 - E ^ 2)), j * F - E * n * (F / (F ^ 2 - E ^ 2)))

def c12Reg (E F M n j s : ℝ) : Set (ℝ × ℝ) :=
  Par (cH E F s (w2Z E F M n j)) (cHv E F (ur1 F)) (cHv E F (ur2 E F)) (pR2 F M j s) (qR E F j - E * n)
def c22Reg (E F M n j s : ℝ) : Set (ℝ × ℝ) :=
  Par (cH E F s (w2W E F M n j)) (cHv E F (ur1 F)) (cHv E F (ur2 E F)) (pR2 F M j s - E * n) (E * n)
def c32Reg (E F M n j s : ℝ) : Set (ℝ × ℝ) :=
  Preg (cH E F s (w2C3 E F M n j)) (cH E F s (w2Z E F M n j)) (cH E F s (w2W E F M n j)) 0
def n2Reg (E F M n j s : ℝ) : Set (ℝ × ℝ) :=
  Preg (cH E F s (w2Qv E F M n j)) (cH E F s (w2W E F M n j)) (cH E F s (w2Z E F M n j)) 0

section R2
variable {E F M n j s : ℝ} (H : RHR E F M n j s)
include H

theorem RHR.rpos : 0 ≤ pR2 F M j s - E * n ∧ 0 ≤ qR E F j - E * n ∧ 0 < E * n ∧ 0 < pR2 F M j s := by
  have h1 := H.hB; have h2 := H.hC; have hE := H.hE; have hn := H.hn
  have : 0 < E * n := by positivity
  unfold pR2 qR
  refine ⟨by linarith, by linarith, this, by linarith⟩

set_option maxHeartbeats 8000000 in
theorem c12_facts (hq1 : 0 < qR E F j - E * n) :
    LF E F s (c12Reg E F M n j s) 0 (-1) 0 ∧ LF E F s (c12Reg E F M n j s) 0 1 (j * F) ∧
    LF E F s (c12Reg E F M n j s) (-1) (-1) (-s) ∧ LF E F s (c12Reg E F M n j s) 1 1 (M + j * F) ∧
    LF E F s (c12Reg E F M n j s) (F ^ 2) (2 * F ^ 2 - E ^ 2) (c5f E F M n j) ∧
    LF E F s (c12Reg E F M n j s) 0 1 (j * F - E * n * (F / (F ^ 2 - E ^ 2))) := by
  obtain ⟨hF, hB, hEF', hn0, hM, hj0, hv, hen⟩ := H.pos
  obtain ⟨-, -, hen', hp0⟩ := H.rpos
  have hE := H.hE
  have hEF := H.hEF
  have hr0 := H.hr0
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> unfold LF c12Reg <;>
    refine par_apex_le s H.hE H.hEF _ _ _ _ _ hp0 hq1 _ _ _ ?_ ?_ ?_ ?_ <;>
    simp only [w2Z, ur1, ur2, pR2, qR, c5f, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;>
    field_simp <;>
    nlinarith [mul_nonneg hj0 hM.le, H.hB, H.hC, mul_pos hE hE, mul_pos hF hB, mul_pos hen' hF, mul_pos hen' hB]

set_option maxHeartbeats 8000000 in
theorem c22_facts (hp1 : 0 < pR2 F M j s - E * n) :
    LF E F s (c22Reg E F M n j s) 0 (-1) 0 ∧ LF E F s (c22Reg E F M n j s) 0 1 (j * F) ∧
    LF E F s (c22Reg E F M n j s) (-1) (-1) (-s) ∧ LF E F s (c22Reg E F M n j s) 1 1 (M + j * F) ∧
    LF E F s (c22Reg E F M n j s) (F ^ 2) (2 * F ^ 2 - E ^ 2) (c5f E F M n j) ∧
    LF E F s (c22Reg E F M n j s) 0 (-1) (-(j * F - E * n * (F / (F ^ 2 - E ^ 2)))) ∧
    LF E F s (c22Reg E F M n j s) 1 1 (M + j * F - E * n / F) := by
  obtain ⟨hF, hB, hEF', hn0, hM, hj0, hv, hen⟩ := H.pos
  obtain ⟨-, -, hen', hp0⟩ := H.rpos
  have hE := H.hE
  have hEF := H.hEF
  have hr0 := H.hr0
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> unfold LF c22Reg <;>
    refine par_apex_le s H.hE H.hEF _ _ _ _ _ hp1 hen' _ _ _ ?_ ?_ ?_ ?_ <;>
    simp only [w2W, ur1, ur2, pR2, qR, c5f, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;>
    field_simp <;>
    nlinarith [mul_nonneg hj0 hM.le, H.hB, H.hC, mul_pos hE hE, mul_pos hF hB, mul_pos hen' hF, mul_pos hen' hB]

set_option maxHeartbeats 8000000 in
theorem c32_facts :
    LF E F s (c32Reg E F M n j s) 0 (-1) 0 ∧ LF E F s (c32Reg E F M n j s) 0 1 (j * F) ∧
    LF E F s (c32Reg E F M n j s) (-1) (-1) (-s) ∧ LF E F s (c32Reg E F M n j s) 1 1 (M + j * F) ∧
    LF E F s (c32Reg E F M n j s) (F ^ 2) (2 * F ^ 2 - E ^ 2) (c5f E F M n j) ∧
    LF E F s (c32Reg E F M n j s) 0 (-1) (-(j * F - E * n * (F / (F ^ 2 - E ^ 2)))) ∧
    LF E F s (c32Reg E F M n j s) (-1) (-1) (-(M + j * F - E * n / F)) := by
  obtain ⟨hF, hB, hEF', hn0, hM, hj0, hv, hen⟩ := H.pos
  obtain ⟨hp1, hq1, hen', hp0⟩ := H.rpos
  have hE := H.hE
  have hEF := H.hEF
  have hr0 := H.hr0
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> unfold LF c32Reg <;>
    refine preg_apex_le s hE hEF _ _ _ _ _ _ _ le_rfl zero_le_one ?_ ?_ ?_ ?_ <;>
    simp only [w2C3, w2Z, w2W, zero_mul, add_zero, c5f] <;>
    field_simp <;>
    nlinarith [mul_nonneg hj0 hM.le, H.hB, H.hC, mul_pos hE hE, mul_pos hF hB, mul_pos hen' hF, mul_pos hen' hB]

set_option maxHeartbeats 8000000 in
theorem n2_facts :
    LF E F s (n2Reg E F M n j s) (-1) 0 0 ∧ LF E F s (n2Reg E F M n j s) 0 (-1) 0 ∧
    LF E F s (n2Reg E F M n j s) (-1) (-1) (-s) ∧ LF E F s (n2Reg E F M n j s) 1 1 (M + j * F) ∧
    LF E F s (n2Reg E F M n j s) (-(F ^ 2)) (-(F ^ 2 - E ^ 2)) (-(c0f E F M n j)) ∧
    LF E F s (n2Reg E F M n j s) (-(F ^ 2)) (-(2 * F ^ 2 - E ^ 2)) (-(c5f E F M n j)) := by
  obtain ⟨hF, hB, hEF', hn0, hM, hj0, hv, hen⟩ := H.pos
  obtain ⟨hp1, hq1, hen', hp0⟩ := H.rpos
  have hE := H.hE
  have hEF := H.hEF
  have hr0 := H.hr0
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> unfold LF n2Reg <;>
    refine preg_apex_le s hE hEF _ _ _ _ _ _ _ le_rfl zero_le_one ?_ ?_ ?_ ?_ <;>
    simp only [w2Qv, w2W, w2Z, zero_mul, add_zero, c0f, c5f] <;>
    field_simp <;>
    nlinarith [mul_nonneg hj0 hM.le, H.hB, H.hC, mul_pos hE hE, mul_pos hF hB, mul_pos hen' hF, mul_pos hen' hB,
      mul_pos hF hr0, mul_pos hE hr0, mul_pos hB hr0, mul_nonneg (mul_nonneg hj0 hF.le) hE.le, mul_pos hF hn0,
      mul_pos hE hF, mul_nonneg hj0 hE.le, mul_nonneg hj0 hF.le]

end R2

end

end Erdos634.Draft.ThetaNotch
