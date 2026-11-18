-- Draft/ThetaOddEFam.lean -- ODD-E formalization, module 3: tile families of the U pieces (scale n1) and of the notch triangle (scale n) for NP4.
-- INTERNAL BUILD ONLY, UNAUDITED beyond internal checks.  No sorry, no native_decide.
/-
Copy of `ThetaNotch3Fam` for `NP4` (natural `k` instead of `j f`; the real parameter of the regions is `P.jR = k / f`).
The notch construction is the project's (Bonfioli); the first instance `theta_13(3,4)` was found by computer search on 2026-11-15;
the family proof is `internal working notes`.  Credit as in `ThetaNotch3Fam`: Paliy (band steps on a seed),
Beeson (48-tile seed), Laczkovich, Zhang, Beeson-Rosu (skew frame).  INTERNAL BUILD ONLY, UNAUDITED beyond internal checks.
-/
import Erdos634.Draft.ThetaOddEStrFam

open scoped Classical
open Erdos634.Geometry Erdos634.CertCoord

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Erdos634.Draft.ThetaNotch
noncomputable section
open Erdos634.Draft.WFrameF Erdos634.Draft.RegionTiling Erdos634.Draft.WBrickF Erdos634.Draft.CollarLayer
open Erdos634.Draft.LadderFam Erdos634.Draft.CollarFam
open Erdos634.Draft.S2L (baseTri tri_eq_of_pts)

namespace NP4
variable (P : NP4)

theorem hgn1 : P.e ≤ P.g * P.n1 := le_trans P.hgn (Nat.mul_le_mul_left _ P.hnn)
theorem hn1 : 1 ≤ P.n1 := le_trans P.hn P.hnn

def vN : ℕ := P.f * P.M - (P.e * P.n1 + P.e)
def gnN : ℕ := P.g * P.n1
def enN : ℕ := P.e * P.n
def fnN : ℕ := P.f * P.n
theorem vle : P.e * P.n1 + P.e ≤ P.f * P.M := by
  have hv := P.rhU.pos.2.2.2.2.2.2.1
  unfold vv at hv
  have : ((P.e * P.n1 + P.e : ℕ) : ℝ) ≤ ((P.f * P.M : ℕ) : ℝ) := by push_cast; linarith
  exact_mod_cast this
theorem vR : (P.vN : ℝ) = vv (P.e : ℝ) P.f P.M P.n1 := by
  unfold vN vv; rw [Nat.cast_sub P.vle]; push_cast; ring
theorem vpos : 0 < P.vN := by
  have : (0 : ℝ) < P.vN := by rw [P.vR]; exact P.rhU.pos.2.2.2.2.2.2.1
  exact_mod_cast this
theorem gnR : (P.gnN : ℝ) = ((P.f : ℝ) - P.e) * P.n1 := by unfold gnN; push_cast; rw [P.hgR]
theorem gnpos : 0 < P.gnN := by have := P.hgn1; have := P.he; unfold gnN; omega
theorem enR : (P.enN : ℝ) = (P.e : ℝ) * P.n := by unfold enN; push_cast; ring
theorem fnR : (P.fnN : ℝ) = (P.f : ℝ) * P.n := by unfold fnN; push_cast; ring
theorem enpos : 0 < P.enN := by have := P.he; have := P.hn; unfold enN; positivity
theorem fnpos : 0 < P.fnN := by
  have := P.hef; have := P.he; have := P.hn; unfold fnN; exact Nat.mul_pos (by omega) (by omega)
theorem hge : P.e ≤ P.gnN := P.hgn1
theorem rhoR' : (P.rho : ℝ) = (P.e : ℝ) * P.M - P.f * P.n1 := P.rhoR
theorem rhopos : 0 < P.rho := P.hr1
theorem frho : P.rho ≤ P.f := P.hrf.le

section vtf
variable {φ : ℝ} (hφ : 1 < φ) (hφE : φ = (P.f : ℝ) / P.e)
include hφE

def vt2Fam : TFam (Phi φ '' vt2Reg (P.e : ℝ) P.f P.M P.n1 P.jR P.s) (Mrow hφ P.e P.f P.he0 P.hef) (P.vN * P.vN) := by
  have H := P.rhU
  obtain ⟨hF, hB, hEF', hn0, hM, hj0, hv, hen⟩ := H.pos
  have hE := H.hE
  have hEF := H.hEF
  have hdet : ((w2V1 (P.e : ℝ) P.f P.M P.n1 P.jR).1 - (uD (P.f : ℝ) P.jR).1) * ((w2V2 (P.e : ℝ) P.f P.M P.n1 P.jR).2 - (uD (P.f : ℝ) P.jR).2) -
      ((w2V2 (P.e : ℝ) P.f P.M P.n1 P.jR).1 - (uD (P.f : ℝ) P.jR).1) * ((w2V1 (P.e : ℝ) P.f P.M P.n1 P.jR).2 - (uD (P.f : ℝ) P.jR).2) ≠ 0 := by
    have e1 : ((w2V1 (P.e : ℝ) P.f P.M P.n1 P.jR).1 - (uD (P.f : ℝ) P.jR).1) * ((w2V2 (P.e : ℝ) P.f P.M P.n1 P.jR).2 - (uD (P.f : ℝ) P.jR).2) -
      ((w2V2 (P.e : ℝ) P.f P.M P.n1 P.jR).1 - (uD (P.f : ℝ) P.jR).1) * ((w2V1 (P.e : ℝ) P.f P.M P.n1 P.jR).2 - (uD (P.f : ℝ) P.jR).2) =
      (vv (P.e : ℝ) P.f P.M P.n1) ^ 2 / ((P.f : ℝ) ^ 2 - (P.e : ℝ) ^ 2) := by
      simp only [uD, w2V1, w2V2]; field_simp; ring
    rw [e1]; exact div_ne_zero (pow_ne_zero 2 hv.ne') hB.ne'
  have hc := cong_base_apex hφ P.e P.f P.he0 P.hef hφE (P.s : ℝ) (uD (P.f : ℝ) P.jR) (w2V1 (P.e : ℝ) P.f P.M P.n1 P.jR)
    (w2V2 (P.e : ℝ) P.f P.M P.n1 P.jR) P.vN P.vpos (det_cH_ne (P.s : ℝ) hE hEF _ _ _ hdet) (((P.f : ℝ) ^ 2 - (P.e : ℝ) ^ 2) ^ 2)
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

theorem sig5R : (((P.gnN - P.e : ℕ) : ℝ)) / (P.gnN : ℝ) = sig5b (P.e : ℝ) P.f P.n1 := by
  have H := P.rhU
  have hg := H.hg1
  have hn := H.hn
  have hgnp : 0 < ((P.f : ℝ) - P.e) * P.n1 := by nlinarith
  rw [Nat.cast_sub P.hge, P.gnR]
  unfold sig5b
  have hge : ((P.f : ℝ) - P.e) ≠ 0 := by linarith
  have hne : (P.n1 : ℝ) ≠ 0 := by linarith
  field_simp

include hφE

def p52Fam : TFam (Phi φ '' p52Reg (P.e : ℝ) P.f P.M P.n1 P.jR P.s) (Mrow hφ P.e P.f P.he0 P.hef)
    (P.gnN * P.gnN - (P.gnN - P.e) * (P.gnN - P.e)) := by
  have H := P.rhU
  obtain ⟨hF, hB, hEF', hn0, hM, hj0, hv, hen⟩ := H.pos
  have hE := H.hE
  have hEF := H.hEF
  have hg := H.hg1
  have hgnp : 0 < ((P.f : ℝ) - P.e) * P.n1 := by nlinarith [H.hn]
  have hdet : ((w2W (P.e : ℝ) P.f P.M P.n1 P.jR).1 - (w2X5 P.M P.n1 P.jR (P.f : ℝ)).1) * ((w2U5 (P.e : ℝ) P.f P.M P.n1 P.jR).2 - (w2X5 P.M P.n1 P.jR (P.f : ℝ)).2) -
      ((w2U5 (P.e : ℝ) P.f P.M P.n1 P.jR).1 - (w2X5 P.M P.n1 P.jR (P.f : ℝ)).1) * ((w2W (P.e : ℝ) P.f P.M P.n1 P.jR).2 - (w2X5 P.M P.n1 P.jR (P.f : ℝ)).2) ≠ 0 := by
    have e1 : ((w2W (P.e : ℝ) P.f P.M P.n1 P.jR).1 - (w2X5 P.M P.n1 P.jR (P.f : ℝ)).1) * ((w2U5 (P.e : ℝ) P.f P.M P.n1 P.jR).2 - (w2X5 P.M P.n1 P.jR (P.f : ℝ)).2) -
      ((w2U5 (P.e : ℝ) P.f P.M P.n1 P.jR).1 - (w2X5 P.M P.n1 P.jR (P.f : ℝ)).1) * ((w2W (P.e : ℝ) P.f P.M P.n1 P.jR).2 - (w2X5 P.M P.n1 P.jR (P.f : ℝ)).2) =
      ((P.f : ℝ) - P.e) * P.n1 * ((P.n1 : ℝ) / P.f * (P.f - P.e)) * ((P.f : ℝ) / (P.e + P.f)) * 0 + ((P.f : ℝ) - P.e) * P.n1 ^ 2 / ((P.e : ℝ) + P.f) := by
      simp only [w2X5, w2W, w2U5]; field_simp; ring
    rw [e1]
    have : 0 < ((P.f : ℝ) - P.e) * P.n1 ^ 2 / ((P.e : ℝ) + P.f) := by
      have : (0 : ℝ) < P.n1 := hn0
      positivity
    simpa using this.ne'
  have hgn := P.gnR
  have hc := cong_base_apex hφ P.e P.f P.he0 P.hef hφE (P.s : ℝ) (w2X5 P.M P.n1 P.jR (P.f : ℝ)) (w2W (P.e : ℝ) P.f P.M P.n1 P.jR)
    (w2U5 (P.e : ℝ) P.f P.M P.n1 P.jR) P.gnN P.gnpos (det_cH_ne (P.s : ℝ) hE hEF _ _ _ hdet) (((P.f : ℝ) ^ 2 - (P.e : ℝ) ^ 2) ^ 2)
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

def p42Fam : TFam (Phi φ '' p42Reg (P.e : ℝ) P.f P.M P.n1 P.jR P.s) (Mrow hφ P.e P.f P.he0 P.hef) (2 * P.f * P.gnN) := by
  have H := P.rhU
  obtain ⟨hF, hB, hEF', hn0, hM, hj0, hv, hen⟩ := H.pos
  have hE := H.hE
  have hEF := H.hEF
  have hdet := det_cell_ne (P.s : ℝ) hE hEF (w2Qv P.e P.f P.M P.n1 P.jR) (uw1 P.e P.f) (uw2 P.e P.f) (uw_det hE hB)
  have hc := cong_cell_apex hφ P.e P.f P.he0 P.hef hφE (P.s : ℝ) (w2Qv P.e P.f P.M P.n1 P.jR) (uw1 P.e P.f) (uw2 P.e P.f) hdet
    (((P.e : ℝ) * P.f) ^ 2) (((P.f : ℝ) ^ 2 - (P.e : ℝ) ^ 2) ^ 2) (((P.f : ℝ) ^ 2) ^ 2)
    (by simp only [qf, w2Qv, uw1, Prod.fst_add, Prod.snd_add]; field_simp; ring)
    (by simp only [qf, w2Qv, uw1, uw2, Prod.fst_add, Prod.snd_add]; field_simp; ring)
    (by simp only [qf, w2Qv, uw2, Prod.fst_add, Prod.snd_add]; field_simp; ring)
    (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)))
  have T := parFam φ hφ _ _ _ P.f P.gnN hdet (Mrow hφ P.e P.f P.he0 P.hef) hc
  refine castTF ?_ rfl T
  unfold p42Reg; rw [P.gnR]

def rp2Fam : TFam (Phi φ '' rp2Reg (P.e : ℝ) P.f P.M P.n1 P.jR P.s) (Mrow hφ P.e P.f P.he0 P.hef) (2 * (P.f - P.rho) * P.rho) := by
  have H := P.rhU
  obtain ⟨hF, hB, hEF', hn0, hM, hj0, hv, hen⟩ := H.pos
  have hE := H.hE
  have hEF := H.hEF
  have hdet := det_cell_ne (P.s : ℝ) hE hEF (w2Vt P.f P.M P.jR) (uw1 P.e P.f) (uw2 P.e P.f) (uw_det hE hB)
  have hc := cong_cell_apex hφ P.e P.f P.he0 P.hef hφE (P.s : ℝ) (w2Vt P.f P.M P.jR) (uw1 P.e P.f) (uw2 P.e P.f) hdet
    (((P.e : ℝ) * P.f) ^ 2) (((P.f : ℝ) ^ 2 - (P.e : ℝ) ^ 2) ^ 2) (((P.f : ℝ) ^ 2) ^ 2)
    (by simp only [qf, w2Vt, uw1, Prod.fst_add, Prod.snd_add]; field_simp; ring)
    (by simp only [qf, w2Vt, uw1, uw2, Prod.fst_add, Prod.snd_add]; field_simp; ring)
    (by simp only [qf, w2Vt, uw2, Prod.fst_add, Prod.snd_add]; field_simp; ring)
    (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)))
  have T := parFam φ hφ _ _ _ (P.f - P.rho) P.rho hdet (Mrow hφ P.e P.f P.he0 P.hef) hc
  refine castTF ?_ rfl T
  unfold rp2Reg; rw [Nat.cast_sub P.frho, P.rhoR]

def rt2Fam : TFam (Phi φ '' rt2Reg (P.e : ℝ) P.f P.M P.n1 P.jR P.s) (Mrow hφ P.e P.f P.he0 P.hef) (P.rho * P.rho) := by
  have H := P.rhU
  obtain ⟨hF, hB, hEF', hn0, hM, hj0, hv, hen⟩ := H.pos
  have hE := H.hE
  have hEF := H.hEF
  have hr0 := H.hr0
  have hdet : ((w2Qp (P.e : ℝ) P.f P.M P.n1 P.jR).1 - (w2Qv (P.e : ℝ) P.f P.M P.n1 P.jR).1) * ((w2Vt (P.f : ℝ) P.M P.jR).2 - (w2Qv (P.e : ℝ) P.f P.M P.n1 P.jR).2) -
      ((w2Vt (P.f : ℝ) P.M P.jR).1 - (w2Qv (P.e : ℝ) P.f P.M P.n1 P.jR).1) * ((w2Qp (P.e : ℝ) P.f P.M P.n1 P.jR).2 - (w2Qv (P.e : ℝ) P.f P.M P.n1 P.jR).2) ≠ 0 := by
    have e1 : ((w2Qp (P.e : ℝ) P.f P.M P.n1 P.jR).1 - (w2Qv (P.e : ℝ) P.f P.M P.n1 P.jR).1) * ((w2Vt (P.f : ℝ) P.M P.jR).2 - (w2Qv (P.e : ℝ) P.f P.M P.n1 P.jR).2) -
      ((w2Vt (P.f : ℝ) P.M P.jR).1 - (w2Qv (P.e : ℝ) P.f P.M P.n1 P.jR).1) * ((w2Qp (P.e : ℝ) P.f P.M P.n1 P.jR).2 - (w2Qv (P.e : ℝ) P.f P.M P.n1 P.jR).2) =
      -(((P.e : ℝ) * P.M - P.f * P.n1) ^ 2 / ((P.f : ℝ) ^ 2 - (P.e : ℝ) ^ 2)) := by
      simp only [w2Qv, w2Qp, w2Vt]; field_simp; ring
    rw [e1]; exact neg_ne_zero.mpr (div_ne_zero (pow_ne_zero 2 hr0.ne') hB.ne')
  have hc := cong_base_apex hφ P.e P.f P.he0 P.hef hφE (P.s : ℝ) (w2Qv (P.e : ℝ) P.f P.M P.n1 P.jR) (w2Qp (P.e : ℝ) P.f P.M P.n1 P.jR)
    (w2Vt (P.f : ℝ) P.M P.jR) P.rho P.rhopos (det_cH_ne (P.s : ℝ) hE hEF _ _ _ hdet) (((P.e : ℝ) * P.f) ^ 2) (((P.f : ℝ) ^ 2) ^ 2)
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

def n2Fam : TFam (Phi φ '' n2Reg (P.e : ℝ) P.f P.M P.n P.jR P.s) (Mrow hφ P.e P.f P.he0 P.hef) (P.fnN * P.fnN) := by
  have H := P.rhR
  obtain ⟨hF, hB, hEF', hn0, hM, hj0, hv, hen⟩ := H.pos
  have hE := H.hE
  have hEF := H.hEF
  have hr0 := H.hr0
  have hdet : ((w2W (P.e : ℝ) P.f P.M P.n P.jR).1 - (w2Qv (P.e : ℝ) P.f P.M P.n P.jR).1) * ((w2Z (P.e : ℝ) P.f P.M P.n P.jR).2 - (w2Qv (P.e : ℝ) P.f P.M P.n P.jR).2) -
      ((w2Z (P.e : ℝ) P.f P.M P.n P.jR).1 - (w2Qv (P.e : ℝ) P.f P.M P.n P.jR).1) * ((w2W (P.e : ℝ) P.f P.M P.n P.jR).2 - (w2Qv (P.e : ℝ) P.f P.M P.n P.jR).2) ≠ 0 := by
    have e1 : ((w2W (P.e : ℝ) P.f P.M P.n P.jR).1 - (w2Qv (P.e : ℝ) P.f P.M P.n P.jR).1) * ((w2Z (P.e : ℝ) P.f P.M P.n P.jR).2 - (w2Qv (P.e : ℝ) P.f P.M P.n P.jR).2) -
      ((w2Z (P.e : ℝ) P.f P.M P.n P.jR).1 - (w2Qv (P.e : ℝ) P.f P.M P.n P.jR).1) * ((w2W (P.e : ℝ) P.f P.M P.n P.jR).2 - (w2Qv (P.e : ℝ) P.f P.M P.n P.jR).2) =
      (P.f : ℝ) ^ 2 * (P.n : ℝ) ^ 2 / ((P.f : ℝ) ^ 2 - (P.e : ℝ) ^ 2) := by
      simp only [w2Qv, w2W, w2Z]; field_simp; ring
    rw [e1]; exact div_ne_zero (mul_ne_zero (pow_ne_zero 2 hF.ne') (pow_ne_zero 2 hn0.ne')) hB.ne'
  have hc := cong_base_apex hφ P.e P.f P.he0 P.hef hφE (P.s : ℝ) (w2Qv P.e P.f P.M P.n P.jR) (w2W P.e P.f P.M P.n P.jR)
    (w2Z P.e P.f P.M P.n P.jR) P.fnN P.fnpos (det_cH_ne (P.s : ℝ) hE hEF _ _ _ hdet) (((P.f : ℝ) ^ 2 - (P.e : ℝ) ^ 2) ^ 2)
    (((P.e : ℝ) * P.f) ^ 2) (((P.f : ℝ) ^ 2) ^ 2)
    (by rw [P.fnR]; simp only [qf, w2Qv, w2W]; field_simp; ring)
    (by rw [P.fnR]; simp only [qf, w2Z, w2W]; field_simp; ring)
    (by rw [P.fnR]; simp only [qf, w2Qv, w2Z]; field_simp; ring)
    (Or.inl ⟨rfl, rfl, rfl⟩)
  have T := ladderFam φ hφ _ _ _ P.fnN 0 P.fnpos (Nat.zero_le _) (det_cH_ne (P.s : ℝ) hE hEF _ _ _ hdet)
    (Mrow hφ P.e P.f P.he0 P.hef) hc
  exact castTF (by simp [n2Reg]) (by simp) T

end rf

end NP4

end

end Erdos634.Draft.ThetaNotch
