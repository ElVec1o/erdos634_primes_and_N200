-- Draft/ThetaNotch2Fam.lean -- STAGE 1b: tile families of the pieces (v-tau, pi5, pi4, rho-tau, rho-par; C1, C2, C3; notch), general (M, n).
-- INTERNAL BUILD ONLY, UNAUDITED (reading audit 2026-11-14, SOUND WITH GAPS, internal audit).  No sorry, no native_decide.
/-
Credit: Paliy, Beeson, Laczkovich, Zhang, Beeson-Rosu; the project.  INTERNAL BUILD ONLY, UNAUDITED.
-/
import Erdos634.Draft.ThetaNotch2PR

open scoped Classical
open Erdos634.Geometry Erdos634.CertCoord

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Erdos634.Draft.ThetaNotch
noncomputable section
open Erdos634.Draft.WFrameF Erdos634.Draft.RegionTiling Erdos634.Draft.WBrickF Erdos634.Draft.CollarLayer
open Erdos634.Draft.LadderFam Erdos634.Draft.CollarFam
open Erdos634.Draft.S2L (baseTri tri_eq_of_pts)

theorem uw_det {E F : ℝ} (hE : 0 < E) (hB : 0 < F ^ 2 - E ^ 2) :
    (uw1 E F).1 * (uw2 E F).2 - (uw2 E F).1 * (uw1 E F).2 ≠ 0 := by
  have e : (uw1 E F).1 * (uw2 E F).2 - (uw2 E F).1 * (uw1 E F).2 = 1 / (F ^ 2 - E ^ 2) := by
    simp only [uw1, uw2]; field_simp; ring
  rw [e]; positivity

namespace NP2
variable (P : NP2)

def vN : ℕ := P.f * P.M - (P.e * P.n + P.e)
def gnN : ℕ := P.g * P.n
def enN : ℕ := P.e * P.n
def fnN : ℕ := P.f * P.n
def ppN : ℕ := (P.M + P.j * P.f - P.s) * P.f
def qqN : ℕ := P.j * P.b

theorem vle : P.e * P.n + P.e ≤ P.f * P.M := by
  have hv := P.rh.pos.2.2.2.2.2.2.1
  unfold vv at hv
  have : ((P.e * P.n + P.e : ℕ) : ℝ) ≤ ((P.f * P.M : ℕ) : ℝ) := by push_cast; linarith
  exact_mod_cast this
theorem vR : (P.vN : ℝ) = vv (P.e : ℝ) P.f P.M P.n := by
  unfold vN vv; rw [Nat.cast_sub P.vle]; push_cast; ring
theorem vpos : 0 < P.vN := by
  have : (0 : ℝ) < P.vN := by rw [P.vR]; exact P.rh.pos.2.2.2.2.2.2.1
  exact_mod_cast this
theorem gnR : (P.gnN : ℝ) = ((P.f : ℝ) - P.e) * P.n := by unfold gnN; push_cast; rw [P.hgR]
theorem enR : (P.enN : ℝ) = (P.e : ℝ) * P.n := by unfold enN; push_cast; ring
theorem fnR : (P.fnN : ℝ) = (P.f : ℝ) * P.n := by unfold fnN; push_cast; ring
theorem gnpos : 0 < P.gnN := by have := P.hgn; have := P.he; unfold gnN; omega
theorem enpos : 0 < P.enN := by have := P.he; have := P.hn; unfold enN; positivity
theorem fnpos : 0 < P.fnN := by
  have := P.hef; have := P.he; have := P.hn; unfold fnN; exact Nat.mul_pos (by omega) (by omega)
theorem hge : P.e ≤ P.gnN := P.hgn
theorem hen_p : P.enN ≤ P.ppN := by
  have h1 : (P.M + P.j * P.f - P.s) * P.f = (P.M + P.j * P.f) * P.f - P.s * P.f := Nat.sub_mul _ _ _
  have h2 := P.hC
  unfold ppN enN; rw [h1]; omega
theorem hen_q : P.enN ≤ P.qqN := by have := P.hB; unfold qqN enN; exact this
theorem ppR : (P.ppN : ℝ) = pR2 (P.f : ℝ) P.M P.j P.s := by
  unfold ppN pR2; rw [Nat.cast_mul, Nat.cast_sub P.hst.le]; push_cast; ring
theorem qqR : (P.qqN : ℝ) = qR (P.e : ℝ) P.f P.j := by
  unfold qqN qR; push_cast; rw [P.hbR]
theorem rhoR' : (P.rho : ℝ) = (P.e : ℝ) * P.M - P.f * P.n := P.rhoR
theorem rhopos : 0 < P.rho := P.hr1
theorem frho : P.rho ≤ P.f := P.hrf.le

section vtf
variable {φ : ℝ} (hφ : 1 < φ) (hφE : φ = (P.f : ℝ) / P.e)
include hφE

def vt2Fam : TFam (Phi φ '' vt2Reg (P.e : ℝ) P.f P.M P.n P.j P.s) (Mrow hφ P.e P.f P.he0 P.hef) (P.vN * P.vN) := by
  have H := P.rh
  obtain ⟨hF, hB, hEF', hn0, hM, hj0, hv, hen⟩ := H.pos
  have hE := H.hE
  have hEF := H.hEF
  have hdet : ((w2V1 (P.e : ℝ) P.f P.M P.n P.j).1 - (uD (P.f : ℝ) P.j).1) * ((w2V2 (P.e : ℝ) P.f P.M P.n P.j).2 - (uD (P.f : ℝ) P.j).2) -
      ((w2V2 (P.e : ℝ) P.f P.M P.n P.j).1 - (uD (P.f : ℝ) P.j).1) * ((w2V1 (P.e : ℝ) P.f P.M P.n P.j).2 - (uD (P.f : ℝ) P.j).2) ≠ 0 := by
    have e1 : ((w2V1 (P.e : ℝ) P.f P.M P.n P.j).1 - (uD (P.f : ℝ) P.j).1) * ((w2V2 (P.e : ℝ) P.f P.M P.n P.j).2 - (uD (P.f : ℝ) P.j).2) -
      ((w2V2 (P.e : ℝ) P.f P.M P.n P.j).1 - (uD (P.f : ℝ) P.j).1) * ((w2V1 (P.e : ℝ) P.f P.M P.n P.j).2 - (uD (P.f : ℝ) P.j).2) =
      (vv (P.e : ℝ) P.f P.M P.n) ^ 2 / ((P.f : ℝ) ^ 2 - (P.e : ℝ) ^ 2) := by
      simp only [uD, w2V1, w2V2]; field_simp; ring
    rw [e1]; exact div_ne_zero (pow_ne_zero 2 hv.ne') hB.ne'
  have hc := cong_base_apex hφ P.e P.f P.he0 P.hef hφE (P.s : ℝ) (uD (P.f : ℝ) P.j) (w2V1 (P.e : ℝ) P.f P.M P.n P.j)
    (w2V2 (P.e : ℝ) P.f P.M P.n P.j) P.vN P.vpos (det_cH_ne (P.s : ℝ) hE hEF _ _ _ hdet) (((P.f : ℝ) ^ 2 - (P.e : ℝ) ^ 2) ^ 2)
    (((P.e : ℝ) * P.f) ^ 2) (((P.f : ℝ) ^ 2) ^ 2)
    (by rw [P.vR]; simp only [qf, uD, w2V1]; field_simp; ring)
    (by rw [P.vR]; simp only [qf, w2V1, w2V2]; field_simp; ring)
    (by rw [P.vR]; simp only [qf, uD, w2V2]; field_simp; ring)
    (Or.inl ⟨rfl, rfl, rfl⟩)
  have T := ladderFam φ hφ _ _ _ P.vN 0 P.vpos (Nat.zero_le _) (det_cH_ne (P.s : ℝ) hE hEF _ _ _ hdet) (Mrow hφ P.e P.f P.he0 P.hef) hc
  exact castTF (by simp [vt2Reg]) (by simp) T

end vtf

section p5f
variable {φ : ℝ} (hφ : 1 < φ) (hφE : φ = (P.f : ℝ) / P.e)

theorem sig5R : (((P.gnN - P.e : ℕ) : ℝ)) / (P.gnN : ℝ) = sig5b (P.e : ℝ) P.f P.n := by
  have H := P.rh
  have hg := H.hg1
  have hn := H.hn
  have hgnp : 0 < ((P.f : ℝ) - P.e) * P.n := by nlinarith
  rw [Nat.cast_sub P.hge, P.gnR]
  unfold sig5b
  have hge : ((P.f : ℝ) - P.e) ≠ 0 := by linarith
  have hne : (P.n : ℝ) ≠ 0 := by linarith
  field_simp

include hφE

def p52Fam : TFam (Phi φ '' p52Reg (P.e : ℝ) P.f P.M P.n P.j P.s) (Mrow hφ P.e P.f P.he0 P.hef)
    (P.gnN * P.gnN - (P.gnN - P.e) * (P.gnN - P.e)) := by
  have H := P.rh
  obtain ⟨hF, hB, hEF', hn0, hM, hj0, hv, hen⟩ := H.pos
  have hE := H.hE
  have hEF := H.hEF
  have hg := H.hg1
  have hgnp : 0 < ((P.f : ℝ) - P.e) * P.n := by nlinarith [H.hn]
  have hdet : ((w2W (P.e : ℝ) P.f P.M P.n P.j).1 - (w2X5 P.M P.n P.j (P.f : ℝ)).1) * ((w2U5 (P.e : ℝ) P.f P.M P.n P.j).2 - (w2X5 P.M P.n P.j (P.f : ℝ)).2) -
      ((w2U5 (P.e : ℝ) P.f P.M P.n P.j).1 - (w2X5 P.M P.n P.j (P.f : ℝ)).1) * ((w2W (P.e : ℝ) P.f P.M P.n P.j).2 - (w2X5 P.M P.n P.j (P.f : ℝ)).2) ≠ 0 := by
    have e1 : ((w2W (P.e : ℝ) P.f P.M P.n P.j).1 - (w2X5 P.M P.n P.j (P.f : ℝ)).1) * ((w2U5 (P.e : ℝ) P.f P.M P.n P.j).2 - (w2X5 P.M P.n P.j (P.f : ℝ)).2) -
      ((w2U5 (P.e : ℝ) P.f P.M P.n P.j).1 - (w2X5 P.M P.n P.j (P.f : ℝ)).1) * ((w2W (P.e : ℝ) P.f P.M P.n P.j).2 - (w2X5 P.M P.n P.j (P.f : ℝ)).2) =
      ((P.f : ℝ) - P.e) * P.n * ((P.n : ℝ) / P.f * (P.f - P.e)) * ((P.f : ℝ) / (P.e + P.f)) * 0 + ((P.f : ℝ) - P.e) * P.n ^ 2 / ((P.e : ℝ) + P.f) := by
      simp only [w2X5, w2W, w2U5]; field_simp; ring
    rw [e1]
    have : 0 < ((P.f : ℝ) - P.e) * P.n ^ 2 / ((P.e : ℝ) + P.f) := by
      have : (0 : ℝ) < P.n := hn0
      positivity
    simpa using this.ne'
  have hgn := P.gnR
  have hc := cong_base_apex hφ P.e P.f P.he0 P.hef hφE (P.s : ℝ) (w2X5 P.M P.n P.j (P.f : ℝ)) (w2W (P.e : ℝ) P.f P.M P.n P.j)
    (w2U5 (P.e : ℝ) P.f P.M P.n P.j) P.gnN P.gnpos (det_cH_ne (P.s : ℝ) hE hEF _ _ _ hdet) (((P.f : ℝ) ^ 2 - (P.e : ℝ) ^ 2) ^ 2)
    (((P.e : ℝ) * P.f) ^ 2) (((P.f : ℝ) ^ 2) ^ 2)
    (by rw [hgn]; simp only [qf, w2X5, w2W]; field_simp; ring)
    (by rw [hgn]; simp only [qf, w2W, w2U5]; field_simp; ring)
    (by rw [hgn]; simp only [qf, w2X5, w2U5]; field_simp; ring)
    (Or.inl ⟨rfl, rfl, rfl⟩)
  have T := ladderFam φ hφ _ _ _ P.gnN (P.gnN - P.e) P.gnpos (Nat.sub_le _ _) (det_cH_ne (P.s : ℝ) hE hEF _ _ _ hdet)
    (Mrow hφ P.e P.f P.he0 P.hef) hc
  refine castTF ?_ rfl T
  unfold p52Reg; rw [sig5R]

end p5f

section p4f
variable {φ : ℝ} (hφ : 1 < φ) (hφE : φ = (P.f : ℝ) / P.e)
include hφE

def p42Fam : TFam (Phi φ '' p42Reg (P.e : ℝ) P.f P.M P.n P.j P.s) (Mrow hφ P.e P.f P.he0 P.hef) (2 * P.f * P.gnN) := by
  have H := P.rh
  obtain ⟨hF, hB, hEF', hn0, hM, hj0, hv, hen⟩ := H.pos
  have hE := H.hE
  have hEF := H.hEF
  have hdet := det_cell_ne (P.s : ℝ) hE hEF (w2Qv P.e P.f P.M P.n P.j) (uw1 P.e P.f) (uw2 P.e P.f) (uw_det hE hB)
  have hc := cong_cell_apex hφ P.e P.f P.he0 P.hef hφE (P.s : ℝ) (w2Qv P.e P.f P.M P.n P.j) (uw1 P.e P.f) (uw2 P.e P.f) hdet
    (((P.e : ℝ) * P.f) ^ 2) (((P.f : ℝ) ^ 2 - (P.e : ℝ) ^ 2) ^ 2) (((P.f : ℝ) ^ 2) ^ 2)
    (by simp only [qf, w2Qv, uw1, Prod.fst_add, Prod.snd_add]; field_simp; ring)
    (by simp only [qf, w2Qv, uw1, uw2, Prod.fst_add, Prod.snd_add]; field_simp; ring)
    (by simp only [qf, w2Qv, uw2, Prod.fst_add, Prod.snd_add]; field_simp; ring)
    (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)))
  have T := parFam φ hφ _ _ _ P.f P.gnN hdet (Mrow hφ P.e P.f P.he0 P.hef) hc
  refine castTF ?_ rfl T
  unfold p42Reg; rw [P.gnR]

def rp2Fam : TFam (Phi φ '' rp2Reg (P.e : ℝ) P.f P.M P.n P.j P.s) (Mrow hφ P.e P.f P.he0 P.hef) (2 * (P.f - P.rho) * P.rho) := by
  have H := P.rh
  obtain ⟨hF, hB, hEF', hn0, hM, hj0, hv, hen⟩ := H.pos
  have hE := H.hE
  have hEF := H.hEF
  have hdet := det_cell_ne (P.s : ℝ) hE hEF (w2Vt P.f P.M P.j) (uw1 P.e P.f) (uw2 P.e P.f) (uw_det hE hB)
  have hc := cong_cell_apex hφ P.e P.f P.he0 P.hef hφE (P.s : ℝ) (w2Vt P.f P.M P.j) (uw1 P.e P.f) (uw2 P.e P.f) hdet
    (((P.e : ℝ) * P.f) ^ 2) (((P.f : ℝ) ^ 2 - (P.e : ℝ) ^ 2) ^ 2) (((P.f : ℝ) ^ 2) ^ 2)
    (by simp only [qf, w2Vt, uw1, Prod.fst_add, Prod.snd_add]; field_simp; ring)
    (by simp only [qf, w2Vt, uw1, uw2, Prod.fst_add, Prod.snd_add]; field_simp; ring)
    (by simp only [qf, w2Vt, uw2, Prod.fst_add, Prod.snd_add]; field_simp; ring)
    (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)))
  have T := parFam φ hφ _ _ _ (P.f - P.rho) P.rho hdet (Mrow hφ P.e P.f P.he0 P.hef) hc
  refine castTF ?_ rfl T
  unfold rp2Reg; rw [Nat.cast_sub P.frho, P.rhoR]

def rt2Fam : TFam (Phi φ '' rt2Reg (P.e : ℝ) P.f P.M P.n P.j P.s) (Mrow hφ P.e P.f P.he0 P.hef) (P.rho * P.rho) := by
  have H := P.rh
  obtain ⟨hF, hB, hEF', hn0, hM, hj0, hv, hen⟩ := H.pos
  have hE := H.hE
  have hEF := H.hEF
  have hr0 := H.hr0
  have hdet : ((w2Qp (P.e : ℝ) P.f P.M P.n P.j).1 - (w2Qv (P.e : ℝ) P.f P.M P.n P.j).1) * ((w2Vt (P.f : ℝ) P.M P.j).2 - (w2Qv (P.e : ℝ) P.f P.M P.n P.j).2) -
      ((w2Vt (P.f : ℝ) P.M P.j).1 - (w2Qv (P.e : ℝ) P.f P.M P.n P.j).1) * ((w2Qp (P.e : ℝ) P.f P.M P.n P.j).2 - (w2Qv (P.e : ℝ) P.f P.M P.n P.j).2) ≠ 0 := by
    have e1 : ((w2Qp (P.e : ℝ) P.f P.M P.n P.j).1 - (w2Qv (P.e : ℝ) P.f P.M P.n P.j).1) * ((w2Vt (P.f : ℝ) P.M P.j).2 - (w2Qv (P.e : ℝ) P.f P.M P.n P.j).2) -
      ((w2Vt (P.f : ℝ) P.M P.j).1 - (w2Qv (P.e : ℝ) P.f P.M P.n P.j).1) * ((w2Qp (P.e : ℝ) P.f P.M P.n P.j).2 - (w2Qv (P.e : ℝ) P.f P.M P.n P.j).2) =
      -(((P.e : ℝ) * P.M - P.f * P.n) ^ 2 / ((P.f : ℝ) ^ 2 - (P.e : ℝ) ^ 2)) := by
      simp only [w2Qv, w2Qp, w2Vt]; field_simp; ring
    rw [e1]; exact neg_ne_zero.mpr (div_ne_zero (pow_ne_zero 2 hr0.ne') hB.ne')
  have hc := cong_base_apex hφ P.e P.f P.he0 P.hef hφE (P.s : ℝ) (w2Qv (P.e : ℝ) P.f P.M P.n P.j) (w2Qp (P.e : ℝ) P.f P.M P.n P.j)
    (w2Vt (P.f : ℝ) P.M P.j) P.rho P.rhopos (det_cH_ne (P.s : ℝ) hE hEF _ _ _ hdet) (((P.e : ℝ) * P.f) ^ 2) (((P.f : ℝ) ^ 2) ^ 2)
    (((P.f : ℝ) ^ 2 - (P.e : ℝ) ^ 2) ^ 2)
    (by rw [P.rhoR']; simp only [qf, w2Qv, w2Qp]; field_simp; ring)
    (by rw [P.rhoR']; simp only [qf, w2Qp, w2Vt]; field_simp; ring)
    (by rw [P.rhoR']; simp only [qf, w2Qv, w2Vt]; field_simp; ring)
    (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))))
  have T := ladderFam φ hφ _ _ _ P.rho 0 P.rhopos (Nat.zero_le _) (det_cH_ne (P.s : ℝ) hE hEF _ _ _ hdet)
    (Mrow hφ P.e P.f P.he0 P.hef) hc
  exact castTF (by simp [rt2Reg]) (by simp) T

end p4f

section rf
variable {φ : ℝ} (hφ : 1 < φ) (hφE : φ = (P.f : ℝ) / P.e)
include hφE

def c12Fam : TFam (Phi φ '' c12Reg (P.e : ℝ) P.f P.M P.n P.j P.s) (Mrow hφ P.e P.f P.he0 P.hef) (2 * P.ppN * (P.qqN - P.enN)) := by
  have H := P.rh
  obtain ⟨hF, hB, hEF', hn0, hM, hj0, hv, hen⟩ := H.pos
  have hE := H.hE
  have hEF := H.hEF
  have hdet := det_cell_ne (P.s : ℝ) hE hEF (w2Z P.e P.f P.M P.n P.j) (ur1 P.f) (ur2 P.e P.f) (ur_det hF hB)
  have hc := cong_cell_apex hφ P.e P.f P.he0 P.hef hφE (P.s : ℝ) (w2Z P.e P.f P.M P.n P.j) (ur1 P.f) (ur2 P.e P.f) hdet
    (((P.f : ℝ) ^ 2 - (P.e : ℝ) ^ 2) ^ 2) (((P.f : ℝ) ^ 2) ^ 2) (((P.e : ℝ) * P.f) ^ 2)
    (by simp only [qf, ur1, Prod.fst_add, Prod.snd_add]; field_simp; ring)
    (by simp only [qf, ur1, ur2, Prod.fst_add, Prod.snd_add]; field_simp; ring)
    (by simp only [qf, ur2, Prod.fst_add, Prod.snd_add]; field_simp; ring)
    (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))
  have T := parFam φ hφ _ _ _ P.ppN (P.qqN - P.enN) hdet (Mrow hφ P.e P.f P.he0 P.hef) hc
  refine castTF ?_ rfl T
  unfold c12Reg; rw [P.ppR, Nat.cast_sub P.hen_q, P.qqR, P.enR]

def c22Fam : TFam (Phi φ '' c22Reg (P.e : ℝ) P.f P.M P.n P.j P.s) (Mrow hφ P.e P.f P.he0 P.hef) (2 * (P.ppN - P.enN) * P.enN) := by
  have H := P.rh
  obtain ⟨hF, hB, hEF', hn0, hM, hj0, hv, hen⟩ := H.pos
  have hE := H.hE
  have hEF := H.hEF
  have hdet := det_cell_ne (P.s : ℝ) hE hEF (w2W P.e P.f P.M P.n P.j) (ur1 P.f) (ur2 P.e P.f) (ur_det hF hB)
  have hc := cong_cell_apex hφ P.e P.f P.he0 P.hef hφE (P.s : ℝ) (w2W P.e P.f P.M P.n P.j) (ur1 P.f) (ur2 P.e P.f) hdet
    (((P.f : ℝ) ^ 2 - (P.e : ℝ) ^ 2) ^ 2) (((P.f : ℝ) ^ 2) ^ 2) (((P.e : ℝ) * P.f) ^ 2)
    (by simp only [qf, ur1, Prod.fst_add, Prod.snd_add]; field_simp; ring)
    (by simp only [qf, ur1, ur2, Prod.fst_add, Prod.snd_add]; field_simp; ring)
    (by simp only [qf, ur2, Prod.fst_add, Prod.snd_add]; field_simp; ring)
    (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))
  have T := parFam φ hφ _ _ _ (P.ppN - P.enN) P.enN hdet (Mrow hφ P.e P.f P.he0 P.hef) hc
  refine castTF ?_ rfl T
  unfold c22Reg; rw [Nat.cast_sub P.hen_p, P.ppR, P.enR]

def c32Fam : TFam (Phi φ '' c32Reg (P.e : ℝ) P.f P.M P.n P.j P.s) (Mrow hφ P.e P.f P.he0 P.hef) (P.enN * P.enN) := by
  have H := P.rh
  obtain ⟨hF, hB, hEF', hn0, hM, hj0, hv, hen⟩ := H.pos
  have hE := H.hE
  have hEF := H.hEF
  have hen' : 0 < (P.e : ℝ) * P.n := by positivity
  have hdet : ((w2Z (P.e : ℝ) P.f P.M P.n P.j).1 - (w2C3 (P.e : ℝ) P.f P.M P.n P.j).1) * ((w2W (P.e : ℝ) P.f P.M P.n P.j).2 - (w2C3 (P.e : ℝ) P.f P.M P.n P.j).2) -
      ((w2W (P.e : ℝ) P.f P.M P.n P.j).1 - (w2C3 (P.e : ℝ) P.f P.M P.n P.j).1) * ((w2Z (P.e : ℝ) P.f P.M P.n P.j).2 - (w2C3 (P.e : ℝ) P.f P.M P.n P.j).2) ≠ 0 := by
    have e1 : ((w2Z (P.e : ℝ) P.f P.M P.n P.j).1 - (w2C3 (P.e : ℝ) P.f P.M P.n P.j).1) * ((w2W (P.e : ℝ) P.f P.M P.n P.j).2 - (w2C3 (P.e : ℝ) P.f P.M P.n P.j).2) -
      ((w2W (P.e : ℝ) P.f P.M P.n P.j).1 - (w2C3 (P.e : ℝ) P.f P.M P.n P.j).1) * ((w2Z (P.e : ℝ) P.f P.M P.n P.j).2 - (w2C3 (P.e : ℝ) P.f P.M P.n P.j).2) =
      ((P.e : ℝ) * P.n) ^ 2 / ((P.f : ℝ) ^ 2 - (P.e : ℝ) ^ 2) := by
      simp only [w2Z, w2C3, w2W]; field_simp; ring
    rw [e1]; exact div_ne_zero (pow_ne_zero 2 hen'.ne') hB.ne'
  have hc := cong_base_apex hφ P.e P.f P.he0 P.hef hφE (P.s : ℝ) (w2C3 P.e P.f P.M P.n P.j) (w2Z P.e P.f P.M P.n P.j)
    (w2W P.e P.f P.M P.n P.j) P.enN P.enpos (det_cH_ne (P.s : ℝ) hE hEF _ _ _ hdet) (((P.f : ℝ) ^ 2 - (P.e : ℝ) ^ 2) ^ 2)
    (((P.f : ℝ) ^ 2) ^ 2) (((P.e : ℝ) * P.f) ^ 2)
    (by rw [P.enR]; simp only [qf, w2C3, w2Z]; field_simp; ring)
    (by rw [P.enR]; simp only [qf, w2Z, w2W]; field_simp; ring)
    (by rw [P.enR]; simp only [qf, w2C3, w2W]; field_simp; ring)
    (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))
  have T := ladderFam φ hφ _ _ _ P.enN 0 P.enpos (Nat.zero_le _) (det_cH_ne (P.s : ℝ) hE hEF _ _ _ hdet)
    (Mrow hφ P.e P.f P.he0 P.hef) hc
  exact castTF (by simp [c32Reg]) (by simp) T

def n2Fam : TFam (Phi φ '' n2Reg (P.e : ℝ) P.f P.M P.n P.j P.s) (Mrow hφ P.e P.f P.he0 P.hef) (P.fnN * P.fnN) := by
  have H := P.rh
  obtain ⟨hF, hB, hEF', hn0, hM, hj0, hv, hen⟩ := H.pos
  have hE := H.hE
  have hEF := H.hEF
  have hr0 := H.hr0
  have hdet : ((w2W (P.e : ℝ) P.f P.M P.n P.j).1 - (w2Qv (P.e : ℝ) P.f P.M P.n P.j).1) * ((w2Z (P.e : ℝ) P.f P.M P.n P.j).2 - (w2Qv (P.e : ℝ) P.f P.M P.n P.j).2) -
      ((w2Z (P.e : ℝ) P.f P.M P.n P.j).1 - (w2Qv (P.e : ℝ) P.f P.M P.n P.j).1) * ((w2W (P.e : ℝ) P.f P.M P.n P.j).2 - (w2Qv (P.e : ℝ) P.f P.M P.n P.j).2) ≠ 0 := by
    have e1 : ((w2W (P.e : ℝ) P.f P.M P.n P.j).1 - (w2Qv (P.e : ℝ) P.f P.M P.n P.j).1) * ((w2Z (P.e : ℝ) P.f P.M P.n P.j).2 - (w2Qv (P.e : ℝ) P.f P.M P.n P.j).2) -
      ((w2Z (P.e : ℝ) P.f P.M P.n P.j).1 - (w2Qv (P.e : ℝ) P.f P.M P.n P.j).1) * ((w2W (P.e : ℝ) P.f P.M P.n P.j).2 - (w2Qv (P.e : ℝ) P.f P.M P.n P.j).2) =
      (P.f : ℝ) ^ 2 * (P.n : ℝ) ^ 2 / ((P.f : ℝ) ^ 2 - (P.e : ℝ) ^ 2) := by
      simp only [w2Qv, w2W, w2Z]; field_simp; ring
    rw [e1]; exact div_ne_zero (mul_ne_zero (pow_ne_zero 2 hF.ne') (pow_ne_zero 2 hn0.ne')) hB.ne'
  have hc := cong_base_apex hφ P.e P.f P.he0 P.hef hφE (P.s : ℝ) (w2Qv P.e P.f P.M P.n P.j) (w2W P.e P.f P.M P.n P.j)
    (w2Z P.e P.f P.M P.n P.j) P.fnN P.fnpos (det_cH_ne (P.s : ℝ) hE hEF _ _ _ hdet) (((P.f : ℝ) ^ 2 - (P.e : ℝ) ^ 2) ^ 2)
    (((P.e : ℝ) * P.f) ^ 2) (((P.f : ℝ) ^ 2) ^ 2)
    (by rw [P.fnR]; simp only [qf, w2Qv, w2W]; field_simp; ring)
    (by rw [P.fnR]; simp only [qf, w2Z, w2W]; field_simp; ring)
    (by rw [P.fnR]; simp only [qf, w2Qv, w2Z]; field_simp; ring)
    (Or.inl ⟨rfl, rfl, rfl⟩)
  have T := ladderFam φ hφ _ _ _ P.fnN 0 P.fnpos (Nat.zero_le _) (det_cH_ne (P.s : ℝ) hE hEF _ _ _ hdet)
    (Mrow hφ P.e P.f P.he0 P.hef) hc
  exact castTF (by simp [n2Reg]) (by simp) T

end rf

end NP2

end

end Erdos634.Draft.ThetaNotch
