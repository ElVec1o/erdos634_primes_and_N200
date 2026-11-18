-- Draft/ThetaNotch3Str.lean -- STAGE 1c: the mirrored T1 strips `theta_{i+1}' minus theta_i'` (common base vertex P = (M,k)), apex data, facts, families.
-- INTERNAL BUILD ONLY, UNAUDITED (reading audit 2026-11-14, SOUND WITH GAPS, internal audit).  No sorry, no native_decide.
/-
In apex coordinates the strip over `theta_i'` (`theta_i' = {y >= k, x+y <= t, F^2 x + B y >= c0(i)}`) is `T_i u R_i` with
  T_i = Preg(Y_i, O_i, U2_i; g/(F+g)),  Y_i = (M-i, k+i), O_i = (M - F(i+1)/E, k + F(i+1)/E), U2_i = (M-i, k + F(g-E)/B),
  R_i = p52Reg at `i` = Preg(As_i, A2_i, U1_i; (g-E)/g), `g = (F-E) i`;
both inside the band `c0(i+1) <= F^2 x + B y <= c0(i)`, separated by the vertical line `x = M - i`.
(The `ThetaUnit` pieces `T`, `R` in the frame `ux = (-1/(eb), 1/(eb))`, `uy = (-1/(fb), 0)` of `rust/audit_notch_20261114`.)
Credit: Paliy (band steps), Beeson-Rosu (frame), the unit theta step `ThetaUnitStep` (this project).  INTERNAL BUILD ONLY, UNAUDITED.
-/
import Erdos634.Draft.ThetaNotch3NP

open scoped Classical
open Erdos634.Geometry Erdos634.CertCoord

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Erdos634.Draft.ThetaNotch
noncomputable section
open Erdos634.Draft.WFrameF Erdos634.Draft.RegionTiling Erdos634.Draft.WBrickF Erdos634.Draft.CollarLayer
open Erdos634.Draft.LadderFam Erdos634.Draft.CollarFam
open Erdos634.Draft.S2L (baseTri tri_eq_of_pts)

/-- base hypotheses of a strip of index `i` (no `hrF`: strips lie below `n1`) -/
structure RHB (E F M i j : ℝ) : Prop where
  hE : 0 < E
  hEF : E < F
  hBE : E < F ^ 2 - E ^ 2
  hn : 1 ≤ i
  hj : 1 ≤ j
  hg1 : 1 ≤ F - E
  hgn : E ≤ (F - E) * i
  hr0 : 0 < E * M - F * i

theorem RHB.pos {E F M i j : ℝ} (H : RHB E F M i j) :
    0 < F ∧ 0 < F ^ 2 - E ^ 2 ∧ 0 < E + F ∧ 0 < i ∧ 0 < M ∧ 0 ≤ j ∧ 0 < vv E F M i ∧ 0 < E * (E * i) :=
  pos_core H.hE H.hEF H.hBE H.hn H.hj H.hgn H.hr0

def sY (M i j F : ℝ) : ℝ × ℝ := (M - i, j * F + i)
def sO (E F M i j : ℝ) : ℝ × ℝ := (M - F * (i + 1) / E, j * F + F * (i + 1) / E)
def sU2 (E F M i j : ℝ) : ℝ × ℝ := (M - i, j * F + F * ((F - E) * i - E) / (F ^ 2 - E ^ 2))

def tsReg (E F M i j s : ℝ) : Set (ℝ × ℝ) :=
  Preg (cH E F s (sY M i j F)) (cH E F s (sO E F M i j)) (cH E F s (sU2 E F M i j)) (((F - E) * i) / (F + (F - E) * i))

/-- the band of the strip of index `i` -/
def sbReg (E F M i j s : ℝ) : Set (ℝ × ℝ) :=
  {p | 0 * ax E F p + (-1) * ay E F s p ≤ -(j * F) ∧ 1 * ax E F p + 1 * ay E F s p ≤ M + j * F ∧
    F ^ 2 * ax E F p + (F ^ 2 - E ^ 2) * ay E F s p ≤ c0f E F M i j ∧
    (-(F ^ 2)) * ax E F p + (-(F ^ 2 - E ^ 2)) * ay E F s p ≤ -(c0f E F M (i + 1) j)}

theorem laf_eq (E F M i j : ℝ) : laf E F M i j = c0f E F M (i + 1) j := by
  unfold laf c0f vv; ring

section S3
variable {E F M i j : ℝ} (s : ℝ) (H : RHB E F M i j)
include H

set_option maxHeartbeats 8000000 in
theorem ts_facts :
    LF E F s (tsReg E F M i j s) 1 0 (M - i) ∧ LF E F s (tsReg E F M i j s) 0 (-1) (-(j * F)) ∧
    LF E F s (tsReg E F M i j s) 1 1 (M + j * F) ∧
    LF E F s (tsReg E F M i j s) (F ^ 2) (F ^ 2 - E ^ 2) (c0f E F M i j) ∧
    LF E F s (tsReg E F M i j s) (-(F ^ 2)) (-(F ^ 2 - E ^ 2)) (-(c0f E F M (i + 1) j)) := by
  obtain ⟨hF, hB, hEF', hn0, hM, hj0, hv, hen⟩ := H.pos
  have hE := H.hE
  have hEF := H.hEF
  have hr0 := H.hr0
  have hgn := H.hgn
  have hg : 0 < F - E := by linarith
  have hgnp : 0 < (F - E) * i := mul_pos hg hn0
  have hs0 : 0 ≤ ((F - E) * i) / (F + (F - E) * i) := by positivity
  have hs1 : ((F - E) * i) / (F + (F - E) * i) ≤ 1 := by
    rw [div_le_one (by positivity)]; linarith
  unfold vv at hv
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> unfold LF tsReg <;>
    refine preg_apex_le s H.hE H.hEF _ _ _ _ _ _ _ hs0 hs1 ?_ ?_ ?_ ?_ <;>
    simp only [sY, sO, sU2, c0f] <;> field_simp <;>
    nlinarith [mul_pos hF hB, mul_pos hE hF, mul_pos hE hB, mul_pos hF hr0, mul_pos hF hv, mul_pos hB hv,
      mul_pos hE hv, mul_pos hE hr0, mul_pos hB hr0, mul_nonneg (sub_nonneg.2 hgn) (mul_nonneg hE.le hg.le),
      mul_nonneg hF.le (mul_nonneg (sub_nonneg.2 hgn) hE.le), mul_nonneg hn0.le (mul_nonneg (sub_nonneg.2 hgn) hE.le),
      mul_pos hn0 hE, mul_nonneg hj0 hF.le, mul_nonneg hj0 hE.le, mul_nonneg (mul_nonneg hj0 hF.le) hE.le]

set_option maxHeartbeats 8000000 in
theorem rs_facts :
    LF E F s (p52Reg E F M i j s) (-1) 0 (-(M - i)) ∧ LF E F s (p52Reg E F M i j s) 0 (-1) (-(j * F)) ∧
    LF E F s (p52Reg E F M i j s) 1 1 (M + j * F) ∧
    LF E F s (p52Reg E F M i j s) (F ^ 2) (F ^ 2 - E ^ 2) (c0f E F M i j) ∧
    LF E F s (p52Reg E F M i j s) (-(F ^ 2)) (-(F ^ 2 - E ^ 2)) (-(c0f E F M (i + 1) j)) := by
  obtain ⟨hF, hB, hEF', hn0, hM, hj0, hv, hen⟩ := H.pos
  have hE := H.hE
  have hEF := H.hEF
  have hr0 := H.hr0
  have hgn := H.hgn
  have hg : 0 < F - E := by linarith
  have hgnp : 0 < (F - E) * i := mul_pos hg hn0
  have hgne : F - E ≠ 0 := hg.ne'
  have hn0' : i ≠ 0 := hn0.ne'
  have hs0 : 0 ≤ sig5b E F i := by
    unfold sig5b; rw [sub_nonneg, div_le_one hgnp]; exact hgn
  have hs1 : sig5b E F i ≤ 1 := by
    unfold sig5b; have : 0 < E / ((F - E) * i) := by positivity
    linarith
  rw [← laf_eq]
  unfold vv at hv
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> unfold LF p52Reg <;>
    refine preg_apex_le s hE hEF _ _ _ _ _ _ _ hs0 hs1 ?_ ?_ ?_ ?_ <;>
    simp only [w2X5, w2W, w2U5, sig5b, vv, c0f, laf] <;> field_simp <;>
    nlinarith [mul_pos hF hB, mul_pos hE hF, mul_pos hE hB, mul_pos hF hr0, mul_pos hF hv, mul_pos hB hv,
      mul_pos hE hv, mul_pos hE hr0, mul_pos hB hr0, mul_nonneg (sub_nonneg.2 hgn) (mul_nonneg hE.le hg.le),
      mul_nonneg hF.le (mul_nonneg (sub_nonneg.2 hgn) hE.le), mul_nonneg hn0.le (mul_nonneg (sub_nonneg.2 hgn) hE.le), mul_pos hn0 hE,
      mul_nonneg hj0 hF.le, mul_nonneg hj0 hE.le, mul_nonneg (mul_nonneg hj0 hF.le) hE.le]

end S3

end

end Erdos634.Draft.ThetaNotch
