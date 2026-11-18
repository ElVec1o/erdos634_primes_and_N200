-- Draft/ThetaNotchPR.lean -- apex data and half-plane facts for the Rh group (C1, C2, C3) and the notch triangle.
-- INTERNAL BUILD ONLY, UNAUDITED (reading audit 2026-11-14, SOUND WITH GAPS, internal audit).  No sorry, no native_decide.
/-
Credit: Paliy, Beeson, Laczkovich, Zhang, Beeson-Rosu; the project.  Pieces of `rust/audit_notch_20261114` (`construct`).
`Rh = {y <= k, s <= x+y <= t}` is the lattice parallelogram `P + [0,p] r1 + [0,q] r2` (`P = (M,k)`, `r1 = (-1/f,0)` a `b`-step,
`r2 = (f/b)(1,-1)` an `a`-step, `p = (t-s) f`, `q = j b`); the corner `(en)tau` at `P` (`en = e n`) is cut out; the rest is the
convex pentagon `C1 u C2 u C3`.  INTERNAL BUILD ONLY, UNAUDITED.
-/
import Erdos634.Draft.ThetaNotchPU

open scoped Classical
open Erdos634.Geometry Erdos634.CertCoord

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Erdos634.Draft.ThetaNotch
noncomputable section
open Erdos634.Draft.WFrameF Erdos634.Draft.RegionTiling Erdos634.Draft.WBrickF Erdos634.Draft.CollarLayer
open Erdos634.Draft.LadderFam Erdos634.Draft.CollarFam
open Erdos634.Draft.S2L (baseTri tri_eq_of_pts)

def uPp (F m j : ℝ) : ℝ × ℝ := (F * m, j * F)
def ur1 (F : ℝ) : ℝ × ℝ := (-1 / F, 0)
def ur2 (E F : ℝ) : ℝ × ℝ := (F / (F ^ 2 - E ^ 2), -F / (F ^ 2 - E ^ 2))
def uC1a (E F m j : ℝ) : ℝ × ℝ := (F * m + E * (E * m) * (F / (F ^ 2 - E ^ 2)), j * F - E * (E * m) * (F / (F ^ 2 - E ^ 2)))
def uC2a (E F m j : ℝ) : ℝ × ℝ := (F * m - E * (E * m) / F, j * F)
def uC3a (E F m j : ℝ) : ℝ × ℝ := (F * m - E * (E * m) / F + E * (E * m) * (F / (F ^ 2 - E ^ 2)), j * F - E * (E * m) * (F / (F ^ 2 - E ^ 2)))
def uZ (E F m j : ℝ) : ℝ × ℝ := uC1a E F m j

def pR (E F m j s : ℝ) : ℝ := (F * (m + j) - s) * F
def qR (E F j : ℝ) : ℝ := j * (F ^ 2 - E ^ 2)

def c1Reg (E F m j s : ℝ) : Set (ℝ × ℝ) :=
  Par (cH E F s (uC1a E F m j)) (cHv E F (ur1 F)) (cHv E F (ur2 E F)) (pR E F m j s) (qR E F j - E * (E * m))
def c2Reg (E F m j s : ℝ) : Set (ℝ × ℝ) :=
  Par (cH E F s (uC2a E F m j)) (cHv E F (ur1 F)) (cHv E F (ur2 E F)) (pR E F m j s - E * (E * m)) (E * (E * m))
def c3Reg (E F m j s : ℝ) : Set (ℝ × ℝ) :=
  Preg (cH E F s (uC3a E F m j)) (cH E F s (uZ E F m j)) (cH E F s (uW E F m j)) 0
def nReg (E F m j s : ℝ) : Set (ℝ × ℝ) :=
  Preg (cH E F s (uVt F m j)) (cH E F s (uW E F m j)) (cH E F s (uZ E F m j)) 0

section R
variable {E F m j s : ℝ} (H : RH E F m j s)
include H

theorem RH.rpos : 0 < pR E F m j s - E * (E * m) ∧ 0 < qR E F j - E * (E * m) ∧ 0 < E * (E * m) ∧ 0 < pR E F m j s := by
  have h1 := H.hB; have h2 := H.hC; have hE := H.hE; have hm := H.hm
  have : 0 < E * (E * m) := by positivity
  unfold pR qR
  refine ⟨by linarith, by linarith, this, by linarith⟩

set_option maxHeartbeats 1600000 in
theorem c1_facts :
    LF E F s (c1Reg E F m j s) 0 (-1) 0 ∧ LF E F s (c1Reg E F m j s) 0 1 (j * F) ∧
    LF E F s (c1Reg E F m j s) (-1) (-1) (-s) ∧ LF E F s (c1Reg E F m j s) 1 1 (F * m + j * F) ∧
    LF E F s (c1Reg E F m j s) (F ^ 2) (2 * F ^ 2 - E ^ 2) ((F * ((F ^ 2 - E ^ 2) * m)) + (2 * F ^ 2 - E ^ 2) * (j * F)) ∧
    LF E F s (c1Reg E F m j s) 0 1 (j * F - E * (E * m) * (F / (F ^ 2 - E ^ 2))) := by
  obtain ⟨hF, hB, hEF', hv, hm0, hj0⟩ := H.pos
  obtain ⟨hp1, hq1, hen, hp0⟩ := H.rpos
  have hE := H.hE
  have hEF := H.hEF
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> unfold LF c1Reg <;>
    refine par_apex_le s H.hE H.hEF _ _ _ _ _ hp0 hq1 _ _ _ ?_ ?_ ?_ ?_ <;>
    simp only [uC1a, ur1, ur2, pR, qR, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;>
    field_simp <;>
    nlinarith [mul_nonneg hm0 hj0, H.hB, H.hC, mul_pos hE hE, mul_pos hF hB, mul_pos hen hF, mul_pos hen hB]


set_option maxHeartbeats 1600000 in
theorem c2_facts :
    LF E F s (c2Reg E F m j s) 0 (-1) 0 ∧ LF E F s (c2Reg E F m j s) 0 1 (j * F) ∧
    LF E F s (c2Reg E F m j s) (-1) (-1) (-s) ∧ LF E F s (c2Reg E F m j s) 1 1 (F * m + j * F) ∧
    LF E F s (c2Reg E F m j s) (F ^ 2) (2 * F ^ 2 - E ^ 2) ((F * ((F ^ 2 - E ^ 2) * m)) + (2 * F ^ 2 - E ^ 2) * (j * F)) ∧
    LF E F s (c2Reg E F m j s) 0 (-1) (-(j * F - E * (E * m) * (F / (F ^ 2 - E ^ 2)))) ∧
    LF E F s (c2Reg E F m j s) 1 1 (F * m + j * F - E * (E * m) / F) := by
  obtain ⟨hF, hB, hEF', hv, hm0, hj0⟩ := H.pos
  obtain ⟨hp1, hq1, hen, hp0⟩ := H.rpos
  have hE := H.hE
  have hEF := H.hEF
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> unfold LF c2Reg <;>
    refine par_apex_le s H.hE H.hEF _ _ _ _ _ hp1 hen _ _ _ ?_ ?_ ?_ ?_ <;>
    simp only [uC2a, ur1, ur2, pR, qR, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;>
    field_simp <;>
    nlinarith [mul_nonneg hm0 hj0, H.hB, H.hC, mul_pos hE hE, mul_pos hF hB, mul_pos hen hF, mul_pos hen hB]

set_option maxHeartbeats 1600000 in
theorem c3_facts :
    LF E F s (c3Reg E F m j s) 0 (-1) 0 ∧ LF E F s (c3Reg E F m j s) 0 1 (j * F) ∧
    LF E F s (c3Reg E F m j s) (-1) (-1) (-s) ∧ LF E F s (c3Reg E F m j s) 1 1 (F * m + j * F) ∧
    LF E F s (c3Reg E F m j s) (F ^ 2) (2 * F ^ 2 - E ^ 2) ((F * ((F ^ 2 - E ^ 2) * m)) + (2 * F ^ 2 - E ^ 2) * (j * F)) ∧
    LF E F s (c3Reg E F m j s) 0 (-1) (-(j * F - E * (E * m) * (F / (F ^ 2 - E ^ 2)))) ∧
    LF E F s (c3Reg E F m j s) (-1) (-1) (-(F * m + j * F - E * (E * m) / F)) := by
  obtain ⟨hF, hB, hEF', hv, hm0, hj0⟩ := H.pos
  obtain ⟨hp1, hq1, hen, hp0⟩ := H.rpos
  have hE := H.hE
  have hEF := H.hEF
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> unfold LF c3Reg <;>
    refine preg_apex_le s hE hEF _ _ _ _ _ _ _ le_rfl zero_le_one ?_ ?_ ?_ ?_ <;>
    simp only [uC3a, uZ, uC1a, uW, zero_mul, add_zero] <;>
    field_simp <;>
    nlinarith [mul_nonneg hm0 hj0, H.hB, H.hC, mul_pos hE hE, mul_pos hF hB, mul_pos hen hF, mul_pos hen hB]

set_option maxHeartbeats 1600000 in
theorem n_facts :
    LF E F s (nReg E F m j s) (-1) 0 0 ∧ LF E F s (nReg E F m j s) 0 (-1) 0 ∧
    LF E F s (nReg E F m j s) (-1) (-1) (-s) ∧ LF E F s (nReg E F m j s) 1 1 (F * m + j * F) ∧
    LF E F s (nReg E F m j s) (-(F ^ 2)) (-(F ^ 2 - E ^ 2)) (-((F ^ 2 - E ^ 2) * (F * m + j * F))) ∧
    LF E F s (nReg E F m j s) (-(F ^ 2)) (-(2 * F ^ 2 - E ^ 2)) (-((F * ((F ^ 2 - E ^ 2) * m)) + (2 * F ^ 2 - E ^ 2) * (j * F))) := by
  obtain ⟨hF, hB, hEF', hv, hm0, hj0⟩ := H.pos
  obtain ⟨hp1, hq1, hen, hp0⟩ := H.rpos
  have hE := H.hE
  have hEF := H.hEF
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> unfold LF nReg <;>
    refine preg_apex_le s hE hEF _ _ _ _ _ _ _ le_rfl zero_le_one ?_ ?_ ?_ ?_ <;>
    simp only [uVt, uW, uZ, uC1a, zero_mul, add_zero] <;>
    field_simp <;>
    nlinarith [mul_nonneg hm0 hj0, H.hB, H.hC, mul_pos hE hE, mul_pos hF hB, mul_pos hen hF, mul_pos hen hB]

end R

end

end Erdos634.Draft.ThetaNotch
