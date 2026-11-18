-- Draft/ThetaNotchFamR.lean -- tile families of the Rh group (C1, C2, C3) and of the notch triangle.
-- INTERNAL BUILD ONLY, UNAUDITED (reading audit 2026-11-14, SOUND WITH GAPS, internal audit).  No sorry, no native_decide.
/-
Credit: Paliy, Beeson, Laczkovich, Zhang, Beeson-Rosu; the project.  INTERNAL BUILD ONLY, UNAUDITED.
-/
import Erdos634.Draft.ThetaNotchU

open scoped Classical
open Erdos634.Geometry Erdos634.CertCoord

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Erdos634.Draft.ThetaNotch
noncomputable section
open Erdos634.Draft.WFrameF Erdos634.Draft.RegionTiling Erdos634.Draft.WBrickF Erdos634.Draft.CollarLayer
open Erdos634.Draft.LadderFam Erdos634.Draft.CollarFam


theorem det_cell {E F : ℝ} (s : ℝ) (a w1 w2 : ℝ × ℝ) :
    ((cH E F s a + cHv E F w1).1 - (cH E F s a).1) * ((cH E F s a + cHv E F w2).2 - (cH E F s a).2) -
      ((cH E F s a + cHv E F w2).1 - (cH E F s a).1) * ((cH E F s a + cHv E F w1).2 - (cH E F s a).2) =
    F * E * (F ^ 2 - E ^ 2) ^ 2 * (w1.1 * w2.2 - w2.1 * w1.2) := by
  simp only [cH, cHv, Prod.fst_add, Prod.snd_add]; ring

theorem det_cell_ne {E F : ℝ} (s : ℝ) (hE : 0 < E) (hEF : E < F) (a w1 w2 : ℝ × ℝ) (h : w1.1 * w2.2 - w2.1 * w1.2 ≠ 0) :
    ((cH E F s a + cHv E F w1).1 - (cH E F s a).1) * ((cH E F s a + cHv E F w2).2 - (cH E F s a).2) -
      ((cH E F s a + cHv E F w2).1 - (cH E F s a).1) * ((cH E F s a + cHv E F w1).2 - (cH E F s a).2) ≠ 0 := by
  obtain ⟨hF, hb⟩ := frame_pos hE hEF
  rw [det_cell s]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero hF.ne' hE.ne') (pow_ne_zero 2 hb.ne')) h

theorem ur_det {E F : ℝ} (hF : 0 < F) (hB : 0 < F ^ 2 - E ^ 2) :
    (ur1 F).1 * (ur2 E F).2 - (ur2 E F).1 * (ur1 F).2 ≠ 0 := by
  have e : (ur1 F).1 * (ur2 E F).2 - (ur2 E F).1 * (ur1 F).2 = 1 / (F ^ 2 - E ^ 2) := by
    simp only [ur1, ur2]; field_simp; ring
  rw [e]; positivity

namespace NP
variable (P : NP)

def pp : ℕ := (P.f * (P.m + P.j) - P.s) * P.f
def qq : ℕ := P.j * P.b
def fn : ℕ := P.f * (P.e * P.m)

theorem hen_p : P.en < P.pp := by
  have h1 : (P.f * (P.m + P.j) - P.s) * P.f = P.f * (P.m + P.j) * P.f - P.s * P.f := Nat.sub_mul _ _ _
  have h2 := P.hC
  unfold pp en; rw [h1]; omega
theorem hen_q : P.en < P.qq := by
  have h2 := P.hB
  unfold qq en; exact h2
theorem ppR : (P.pp : ℝ) = pR (P.e : ℝ) P.f P.m P.j P.s := by
  unfold pp pR; rw [Nat.cast_mul, Nat.cast_sub P.hst.le]; push_cast; ring
theorem qqR : (P.qq : ℝ) = qR (P.e : ℝ) P.f P.j := by
  unfold qq qR; push_cast; rw [P.hbR]
theorem fnR : (P.fn : ℝ) = (P.f : ℝ) * ((P.e : ℝ) * P.m) := by unfold fn; push_cast; ring
theorem enpos : 0 < P.en := by have := P.he; have := P.hm; unfold en; positivity
theorem fnpos : 0 < P.fn := Nat.mul_pos (by have := P.hef; have := P.he; omega) (Nat.mul_pos P.he P.hm)

section rf
variable {φ : ℝ} (hφ : 1 < φ) (hφE : φ = (P.f : ℝ) / P.e)
include hφE

/-- `C1`: the parallelogram `Pp + en r2 + [0,p] r1 + [0,q-en] r2` of lattice cells -/
def c1Fam : TFam (Phi φ '' c1Reg (P.e : ℝ) P.f P.m P.j P.s) (Mrow hφ P.e P.f P.he0 P.hef) (2 * P.pp * (P.qq - P.en)) := by
  have H := P.rh
  obtain ⟨hF, hB, hEF', hv, hm0, hj0⟩ := H.pos
  have hE := H.hE
  have hEF := H.hEF
  have hdet : ((cH (P.e : ℝ) P.f P.s (uC1a P.e P.f P.m P.j) + cHv (P.e : ℝ) P.f (ur1 P.f)).1 - (cH (P.e : ℝ) P.f P.s (uC1a P.e P.f P.m P.j)).1) *
      ((cH (P.e : ℝ) P.f P.s (uC1a P.e P.f P.m P.j) + cHv (P.e : ℝ) P.f (ur2 P.e P.f)).2 - (cH (P.e : ℝ) P.f P.s (uC1a P.e P.f P.m P.j)).2) -
      ((cH (P.e : ℝ) P.f P.s (uC1a P.e P.f P.m P.j) + cHv (P.e : ℝ) P.f (ur2 P.e P.f)).1 - (cH (P.e : ℝ) P.f P.s (uC1a P.e P.f P.m P.j)).1) *
      ((cH (P.e : ℝ) P.f P.s (uC1a P.e P.f P.m P.j) + cHv (P.e : ℝ) P.f (ur1 P.f)).2 - (cH (P.e : ℝ) P.f P.s (uC1a P.e P.f P.m P.j)).2) ≠ 0 := by
    have e1 : ((cH (P.e : ℝ) P.f P.s (uC1a P.e P.f P.m P.j) + cHv (P.e : ℝ) P.f (ur1 P.f)).1 - (cH (P.e : ℝ) P.f P.s (uC1a P.e P.f P.m P.j)).1) *
      ((cH (P.e : ℝ) P.f P.s (uC1a P.e P.f P.m P.j) + cHv (P.e : ℝ) P.f (ur2 P.e P.f)).2 - (cH (P.e : ℝ) P.f P.s (uC1a P.e P.f P.m P.j)).2) -
      ((cH (P.e : ℝ) P.f P.s (uC1a P.e P.f P.m P.j) + cHv (P.e : ℝ) P.f (ur2 P.e P.f)).1 - (cH (P.e : ℝ) P.f P.s (uC1a P.e P.f P.m P.j)).1) *
      ((cH (P.e : ℝ) P.f P.s (uC1a P.e P.f P.m P.j) + cHv (P.e : ℝ) P.f (ur1 P.f)).2 - (cH (P.e : ℝ) P.f P.s (uC1a P.e P.f P.m P.j)).2) =
      (P.f : ℝ) * P.e * ((P.f : ℝ) ^ 2 - (P.e : ℝ) ^ 2) := by
      simp only [cH, cHv, ur1, ur2, Prod.fst_add, Prod.snd_add]; field_simp; ring
    rw [e1]; positivity
  have hc := cong_cell_apex hφ P.e P.f P.he0 P.hef hφE (P.s : ℝ) (uC1a P.e P.f P.m P.j) (ur1 P.f) (ur2 P.e P.f) hdet
    (((P.f : ℝ) ^ 2 - (P.e : ℝ) ^ 2) ^ 2) (((P.f : ℝ) ^ 2) ^ 2) (((P.e : ℝ) * P.f) ^ 2)
    (by simp only [qf, ur1, Prod.fst_add, Prod.snd_add]; field_simp; ring)
    (by simp only [qf, ur1, ur2, Prod.fst_add, Prod.snd_add]; field_simp; ring)
    (by simp only [qf, ur2, Prod.fst_add, Prod.snd_add]; field_simp; ring)
    (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))
  have T := parFam φ hφ _ _ _ P.pp (P.qq - P.en) hdet (Mrow hφ P.e P.f P.he0 P.hef) hc
  refine castTF ?_ rfl T
  unfold c1Reg; rw [P.ppR, Nat.cast_sub P.hen_q.le, P.qqR, P.enR]

end rf


section rf2
variable {φ : ℝ} (hφ : 1 < φ) (hφE : φ = (P.f : ℝ) / P.e)
include hφE

/-- `C2`: the parallelogram `Pp + en r1 + [0,p-en] r1 + [0,en] r2` -/
def c2Fam : TFam (Phi φ '' c2Reg (P.e : ℝ) P.f P.m P.j P.s) (Mrow hφ P.e P.f P.he0 P.hef) (2 * (P.pp - P.en) * P.en) := by
  have H := P.rh
  obtain ⟨hF, hB, hEF', hv, hm0, hj0⟩ := H.pos
  have hE := H.hE
  have hEF := H.hEF
  have hdet := det_cell_ne (P.s : ℝ) hE hEF (uC2a P.e P.f P.m P.j) (ur1 P.f) (ur2 P.e P.f) (ur_det hF hB)
  have hc := cong_cell_apex hφ P.e P.f P.he0 P.hef hφE (P.s : ℝ) (uC2a P.e P.f P.m P.j) (ur1 P.f) (ur2 P.e P.f) hdet
    (((P.f : ℝ) ^ 2 - (P.e : ℝ) ^ 2) ^ 2) (((P.f : ℝ) ^ 2) ^ 2) (((P.e : ℝ) * P.f) ^ 2)
    (by simp only [qf, ur1, Prod.fst_add, Prod.snd_add]; field_simp; ring)
    (by simp only [qf, ur1, ur2, Prod.fst_add, Prod.snd_add]; field_simp; ring)
    (by simp only [qf, ur2, Prod.fst_add, Prod.snd_add]; field_simp; ring)
    (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))
  have T := parFam φ hφ _ _ _ (P.pp - P.en) P.en hdet (Mrow hφ P.e P.f P.he0 P.hef) hc
  refine castTF ?_ rfl T
  unfold c2Reg; rw [Nat.cast_sub P.hen_p.le, P.ppR, P.enR]

/-- `C3`: the scaled tile of scale `en` with apex `a3 = Pp + en r1 + en r2` and sides along `-r1`, `-r2` -/
def c3Fam : TFam (Phi φ '' c3Reg (P.e : ℝ) P.f P.m P.j P.s) (Mrow hφ P.e P.f P.he0 P.hef) (P.en * P.en) := by
  have H := P.rh
  obtain ⟨hF, hB, hEF', hv, hm0, hj0⟩ := H.pos
  have hE := H.hE
  have hEF := H.hEF
  have hm := H.hm
  have hmp0 : 0 < (P.m : ℝ) := by linarith [H.hm]
  have hen : 0 < (P.e : ℝ) * (P.e * P.m) := mul_pos hE (mul_pos hE hmp0)
  have hdet : ((uZ P.e P.f P.m P.j).1 - (uC3a P.e P.f P.m P.j).1) * ((uW P.e P.f P.m P.j).2 - (uC3a P.e P.f P.m P.j).2) -
      ((uW P.e P.f P.m P.j).1 - (uC3a P.e P.f P.m P.j).1) * ((uZ P.e P.f P.m P.j).2 - (uC3a P.e P.f P.m P.j).2) ≠ 0 := by
    have e1 : ((uZ P.e P.f P.m P.j).1 - (uC3a P.e P.f P.m P.j).1) * ((uW P.e P.f P.m P.j).2 - (uC3a P.e P.f P.m P.j).2) -
      ((uW P.e P.f P.m P.j).1 - (uC3a P.e P.f P.m P.j).1) * ((uZ P.e P.f P.m P.j).2 - (uC3a P.e P.f P.m P.j).2) =
      ((P.e : ℝ) * (P.e * P.m)) ^ 2 / ((P.f : ℝ) ^ 2 - (P.e : ℝ) ^ 2) := by
      simp only [uZ, uC1a, uC3a, uW]; field_simp; ring
    rw [e1]; exact div_ne_zero (pow_ne_zero 2 hen.ne') hB.ne'
  have hc := cong_base_apex hφ P.e P.f P.he0 P.hef hφE (P.s : ℝ) (uC3a P.e P.f P.m P.j) (uZ P.e P.f P.m P.j)
    (uW P.e P.f P.m P.j) P.en P.enpos (det_cH_ne (P.s : ℝ) hE hEF _ _ _ hdet) (((P.f : ℝ) ^ 2 - (P.e : ℝ) ^ 2) ^ 2)
    (((P.f : ℝ) ^ 2) ^ 2) (((P.e : ℝ) * P.f) ^ 2)
    (by rw [P.enR]; simp only [qf, uC3a, uZ, uC1a]; field_simp; ring)
    (by rw [P.enR]; simp only [qf, uZ, uC1a, uW]; field_simp; ring)
    (by rw [P.enR]; simp only [qf, uC3a, uW]; field_simp; ring)
    (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))
  have T := ladderFam φ hφ _ _ _ P.en 0 P.enpos (Nat.zero_le _) (det_cH_ne (P.s : ℝ) hE hEF _ _ _ hdet)
    (Mrow hφ P.e P.f P.he0 P.hef) hc
  exact castTF (by simp [c3Reg]) (by simp) T

/-- the notch triangle `(fn)tau`: apex `Q' = V2 = (0,t)`, `P2' = W`, `Z` -/
def nFam : TFam (Phi φ '' nReg (P.e : ℝ) P.f P.m P.j P.s) (Mrow hφ P.e P.f P.he0 P.hef) (P.fn * P.fn) := by
  have H := P.rh
  obtain ⟨hF, hB, hEF', hv, hm0, hj0⟩ := H.pos
  have hE := H.hE
  have hEF := H.hEF
  have hm := H.hm
  have hmp0 : 0 < (P.m : ℝ) := by linarith [H.hm]
  have hen : 0 < (P.e : ℝ) * (P.e * P.m) := mul_pos hE (mul_pos hE hmp0)
  have hmp : 0 < (P.m : ℝ) := by linarith
  have hdet : ((uW P.e P.f P.m P.j).1 - (uVt P.f P.m P.j).1) * ((uZ P.e P.f P.m P.j).2 - (uVt P.f P.m P.j).2) -
      ((uZ P.e P.f P.m P.j).1 - (uVt P.f P.m P.j).1) * ((uW P.e P.f P.m P.j).2 - (uVt P.f P.m P.j).2) ≠ 0 := by
    have e1 : ((uW P.e P.f P.m P.j).1 - (uVt P.f P.m P.j).1) * ((uZ P.e P.f P.m P.j).2 - (uVt P.f P.m P.j).2) -
      ((uZ P.e P.f P.m P.j).1 - (uVt P.f P.m P.j).1) * ((uW P.e P.f P.m P.j).2 - (uVt P.f P.m P.j).2) =
      (P.e : ℝ) ^ 2 * P.m * (P.m + (P.e : ℝ) * (P.e * P.m) / ((P.f : ℝ) ^ 2 - (P.e : ℝ) ^ 2)) := by
      simp only [uZ, uC1a, uVt, uW]; field_simp; ring
    rw [e1]; have : 0 < (P.e : ℝ) ^ 2 * P.m * (P.m + (P.e : ℝ) * (P.e * P.m) / ((P.f : ℝ) ^ 2 - (P.e : ℝ) ^ 2)) := by positivity
    exact this.ne'
  have hc := cong_base_apex hφ P.e P.f P.he0 P.hef hφE (P.s : ℝ) (uVt P.f P.m P.j) (uW P.e P.f P.m P.j)
    (uZ P.e P.f P.m P.j) P.fn P.fnpos (det_cH_ne (P.s : ℝ) hE hEF _ _ _ hdet) (((P.f : ℝ) ^ 2 - (P.e : ℝ) ^ 2) ^ 2)
    (((P.e : ℝ) * P.f) ^ 2) (((P.f : ℝ) ^ 2) ^ 2)
    (by rw [P.fnR]; simp only [qf, uVt, uW]; field_simp; ring)
    (by rw [P.fnR]; simp only [qf, uZ, uC1a, uW]; field_simp; ring)
    (by rw [P.fnR]; simp only [qf, uVt, uZ, uC1a]; field_simp; ring)
    (Or.inl ⟨rfl, rfl, rfl⟩)
  have T := ladderFam φ hφ _ _ _ P.fn 0 P.fnpos (Nat.zero_le _) (det_cH_ne (P.s : ℝ) hE hEF _ _ _ hdet)
    (Mrow hφ P.e P.f P.he0 P.hef) hc
  exact castTF (by simp [nReg]) (by simp) T

end rf2

end NP

end

end Erdos634.Draft.ThetaNotch
