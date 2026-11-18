-- Draft/ThetaOddEPos.lean -- ODD-E formalization, module 1: the notch fact lemmas for a base strip with 0 < j (not 1 <= j).
-- INTERNAL BUILD ONLY, UNAUDITED beyond internal checks.  No sorry, no native_decide.
/-
`ThetaNotch2NP.RHU/RHR` and `ThetaNotch3Str.RHB` demand `1 <= j`, but `j = k/f` is `< 1` when `k < f` (most witnesses of Theorem B).
The hypothesis `1 <= j` is used only to obtain `0 <= j` (`pos_core`).  This module re-states the structures with `0 < j` (suffix `B`) and
copies, verbatim except for the names, the fact lemmas `vt2_facts, p52_facts, p42_facts, rt2_facts, rp2_facts` (`ThetaNotch2PU`),
`n2_facts` (`ThetaNotch2PR`), `ts_facts, rs_facts` (`ThetaNotch3Str`).  The notch construction is the project's (Bonfioli);
credit as in those files: Paliy (band steps on a seed), Beeson (48-tile seed), Laczkovich, Zhang, Beeson-Rosu (skew frame).
INTERNAL BUILD ONLY, UNAUDITED beyond internal checks.
-/
import Erdos634.Draft.ThetaNotch3Main

open scoped Classical
open Erdos634.Geometry Erdos634.CertCoord

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Erdos634.Draft.ThetaNotch
noncomputable section

structure RHUB (E F M n j : ℝ) : Prop where
  hE : 0 < E
  hEF : E < F
  hBE : E < F ^ 2 - E ^ 2
  hn : 1 ≤ n
  hj : 0 < j
  hg1 : 1 ≤ F - E
  hgn : E ≤ (F - E) * n
  hr0 : 0 < E * M - F * n
  hrF : E * M - F * n < F

structure RHRB (E F M n j s : ℝ) : Prop where
  hE : 0 < E
  hEF : E < F
  hBE : E < F ^ 2 - E ^ 2
  hn : 1 ≤ n
  hj : 0 < j
  hg1 : 1 ≤ F - E
  hgn : E ≤ (F - E) * n
  hr0 : 0 < E * M - F * n
  hB : E * n ≤ j * (F ^ 2 - E ^ 2)
  hC : E * n ≤ (M + j * F - s) * F
  hD : E ≤ (F - E) * (s - j * F)
  hks : j * F < s
  hst : s < M + j * F

structure RHBB (E F M i j : ℝ) : Prop where
  hE : 0 < E
  hEF : E < F
  hBE : E < F ^ 2 - E ^ 2
  hn : 1 ≤ i
  hj : 0 < j
  hg1 : 1 ≤ F - E
  hgn : E ≤ (F - E) * i
  hr0 : 0 < E * M - F * i

theorem pos_coreB {E F M n j : ℝ} (hE : 0 < E) (hEF : E < F) (hBE : E < F ^ 2 - E ^ 2) (hn : 1 ≤ n) (hj : 0 < j)
    (hgn : E ≤ (F - E) * n) (hr0 : 0 < E * M - F * n) :
    0 < F ∧ 0 < F ^ 2 - E ^ 2 ∧ 0 < E + F ∧ 0 < n ∧ 0 < M ∧ 0 ≤ j ∧ 0 < vv E F M n ∧ 0 < E * (E * n) := by
  have hF : 0 < F := by linarith
  have hB : 0 < F ^ 2 - E ^ 2 := by linarith
  have hn0 : 0 < n := by linarith
  have hM : 0 < M := by
    by_contra h; push_neg at h; nlinarith [mul_nonneg hE.le (neg_nonneg.2 h), mul_pos hF hn0]
  have h1 : E * (F + E) ≤ (F ^ 2 - E ^ 2) * n := by nlinarith [mul_le_mul_of_nonneg_left hgn (by linarith : (0 : ℝ) ≤ F + E)]
  have h2 : 0 < E * vv E F M n := by
    unfold vv; nlinarith [mul_pos hF hr0, mul_pos hE hE]
  have hv : 0 < vv E F M n := by
    by_contra hc; push_neg at hc; nlinarith [mul_nonneg hE.le (neg_nonneg.2 hc)]
  exact ⟨hF, hB, by linarith, hn0, hM, hj.le, hv, by positivity⟩

theorem RHUB.pos {E F M n j : ℝ} (H : RHUB E F M n j) :
    0 < F ∧ 0 < F ^ 2 - E ^ 2 ∧ 0 < E + F ∧ 0 < n ∧ 0 < M ∧ 0 ≤ j ∧ 0 < vv E F M n ∧ 0 < E * (E * n) :=
  pos_coreB H.hE H.hEF H.hBE H.hn H.hj H.hgn H.hr0

theorem RHRB.pos {E F M n j s : ℝ} (H : RHRB E F M n j s) :
    0 < F ∧ 0 < F ^ 2 - E ^ 2 ∧ 0 < E + F ∧ 0 < n ∧ 0 < M ∧ 0 ≤ j ∧ 0 < vv E F M n ∧ 0 < E * (E * n) :=
  pos_coreB H.hE H.hEF H.hBE H.hn H.hj H.hgn H.hr0

theorem RHBB.pos {E F M i j : ℝ} (H : RHBB E F M i j) :
    0 < F ∧ 0 < F ^ 2 - E ^ 2 ∧ 0 < E + F ∧ 0 < i ∧ 0 < M ∧ 0 ≤ j ∧ 0 < vv E F M i ∧ 0 < E * (E * i) :=
  pos_coreB H.hE H.hEF H.hBE H.hn H.hj H.hgn H.hr0

section U2
variable {E F M n j : ℝ} (s : ℝ) (H : RHUB E F M n j)
include H

set_option maxHeartbeats 8000000 in
theorem vt2_factsB :
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
theorem p52_factsB :
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
theorem p42_factsB :
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
theorem rt2_factsB :
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
theorem rp2_factsB :
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
section R2
variable {E F M n j s : ℝ} (H : RHRB E F M n j s)
include H

theorem RHRB.rpos : 0 ≤ pR2 F M j s - E * n ∧ 0 ≤ qR E F j - E * n ∧ 0 < E * n ∧ 0 < pR2 F M j s := by
  have h1 := H.hB; have h2 := H.hC; have hE := H.hE; have hn := H.hn
  have : 0 < E * n := by positivity
  unfold pR2 qR
  refine ⟨by linarith, by linarith, this, by linarith⟩

set_option maxHeartbeats 8000000 in
theorem n2_factsB :
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

section S3
variable {E F M i j : ℝ} (s : ℝ) (H : RHBB E F M i j)
include H

set_option maxHeartbeats 8000000 in
theorem ts_factsB :
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
theorem rs_factsB :
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
