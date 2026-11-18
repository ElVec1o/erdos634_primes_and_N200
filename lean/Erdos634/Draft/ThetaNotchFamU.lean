-- Draft/ThetaNotchFamU.lean -- tile families of the U group (v-tau, pi5, pi4) for the notch seed.
-- INTERNAL BUILD ONLY, UNAUDITED (reading audit 2026-11-14, SOUND WITH GAPS, internal audit).  No sorry, no native_decide.
/-
Credit: Paliy, Beeson, Laczkovich, Zhang, Beeson-Rosu; the project.  INTERNAL BUILD ONLY, UNAUDITED.
-/
import Erdos634.Draft.ThetaNotchNP

open scoped Classical
open Erdos634.Geometry Erdos634.CertCoord

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Erdos634.Draft.ThetaNotch
noncomputable section
open Erdos634.Draft.WFrameF Erdos634.Draft.RegionTiling Erdos634.Draft.WBrickF Erdos634.Draft.CollarLayer
open Erdos634.Draft.LadderFam Erdos634.Draft.CollarFam
open Erdos634.Draft.S2L (baseTri tri_eq_of_pts)

/-- transport a tile family along equal regions and equal counts -/
def castTF {S S' : Set Plane} {M : Erdos634.Geometry.Tri} {n n' : ℕ} (h : S = S') (hn : n = n')
    (R : TFam S M n) : TFam S' M n' := by
  subst h; subst hn; exact R

namespace NP
variable (P : NP)

def v : ℕ := P.b * P.m - P.e
def gn : ℕ := P.g * (P.e * P.m)
def en : ℕ := P.e * (P.e * P.m)

theorem he0 : 0 < P.e := P.he
theorem hef : P.e < P.f := by have := P.hfg; have := P.hg; omega
theorem hEF : (P.e : ℝ) < P.f := by exact_mod_cast P.hef
theorem hbR : (P.b : ℝ) = (P.f : ℝ) ^ 2 - (P.e : ℝ) ^ 2 := by
  have : ((P.f * P.f : ℕ) : ℝ) = ((P.e * P.e + P.b : ℕ) : ℝ) := by rw [P.hb]
  push_cast at this; nlinarith
theorem hgR : (P.g : ℝ) = (P.f : ℝ) - P.e := by
  have : (P.f : ℝ) = P.e + P.g := by exact_mod_cast P.hfg
  linarith
theorem hbe : P.e ≤ P.b * P.m := by
  have h1 : P.e * P.e + P.b = P.f * P.f := P.hb.symm
  have h2 := P.hfg
  have h3 := P.hg
  have h4 := P.hm
  have : P.e < P.b := by nlinarith
  nlinarith
theorem vR : (P.v : ℝ) = ((P.f : ℝ) ^ 2 - (P.e : ℝ) ^ 2) * P.m - P.e := by
  unfold v; rw [Nat.cast_sub P.hbe]; push_cast; rw [P.hbR]
theorem hge : P.e ≤ P.gn := by
  unfold gn; have := P.hg; have := P.hm; have := P.he; nlinarith [Nat.mul_le_mul P.hg P.hm]
theorem gnR : (P.gn : ℝ) = ((P.f : ℝ) - P.e) * (P.e * P.m) := by
  unfold gn; push_cast; rw [P.hgR]
theorem enR : (P.en : ℝ) = (P.e : ℝ) * (P.e * P.m) := by unfold en; push_cast; ring
theorem vpos : 0 < P.v := by
  have : (0 : ℝ) < P.v := by rw [P.vR]; exact P.rh.pos.2.2.2.1
  exact_mod_cast this
theorem gnpos : 0 < P.gn := by
  have := P.hge; have := P.he; omega


section vtf
variable {φ : ℝ} (hφ : 1 < φ) (hφE : φ = (P.f : ℝ) / P.e)
include hφE

/-- the family of the `v`-tau piece: the scaled tile of scale `v` at the corner `D = (0,k)` -/
def vtFam : TFam (Phi φ '' vtReg (P.e : ℝ) P.f P.m P.j P.s) (Mrow hφ P.e P.f P.he0 P.hef) (P.v * P.v) := by
  have H := P.rh
  obtain ⟨hF, hB, hEF', hv, hm0, hj0⟩ := H.pos
  have hE := H.hE
  have hEF := H.hEF
  have hdet : ((uV1 (P.e : ℝ) P.f P.m P.j).1 - (uD (P.f : ℝ) P.j).1) * ((uV2 (P.e : ℝ) P.f P.m P.j).2 - (uD (P.f : ℝ) P.j).2) -
      ((uV2 (P.e : ℝ) P.f P.m P.j).1 - (uD (P.f : ℝ) P.j).1) * ((uV1 (P.e : ℝ) P.f P.m P.j).2 - (uD (P.f : ℝ) P.j).2) ≠ 0 := by
    have e1 : ((uV1 (P.e : ℝ) P.f P.m P.j).1 - (uD (P.f : ℝ) P.j).1) * ((uV2 (P.e : ℝ) P.f P.m P.j).2 - (uD (P.f : ℝ) P.j).2) -
      ((uV2 (P.e : ℝ) P.f P.m P.j).1 - (uD (P.f : ℝ) P.j).1) * ((uV1 (P.e : ℝ) P.f P.m P.j).2 - (uD (P.f : ℝ) P.j).2) =
      (((P.f : ℝ) ^ 2 - (P.e : ℝ) ^ 2) * P.m - P.e) ^ 2 / ((P.f : ℝ) ^ 2 - (P.e : ℝ) ^ 2) := by
      simp only [uD, uV1, uV2]; field_simp; ring
    rw [e1]; exact div_ne_zero (pow_ne_zero 2 hv.ne') hB.ne'
  have hc := cong_base_apex hφ P.e P.f P.he0 P.hef hφE (P.s : ℝ) (uD (P.f : ℝ) P.j) (uV1 (P.e : ℝ) P.f P.m P.j)
    (uV2 (P.e : ℝ) P.f P.m P.j) P.v P.vpos (det_cH_ne (P.s : ℝ) hE hEF _ _ _ hdet) (((P.f : ℝ) ^ 2 - (P.e : ℝ) ^ 2) ^ 2)
    (((P.e : ℝ) * P.f) ^ 2) (((P.f : ℝ) ^ 2) ^ 2)
    (by rw [P.vR]; simp only [qf, uD, uV1]; field_simp; ring)
    (by rw [P.vR]; simp only [qf, uV1, uV2]; field_simp; ring)
    (by rw [P.vR]; simp only [qf, uD, uV2]; field_simp; ring)
    (Or.inl ⟨rfl, rfl, rfl⟩)
  have T := ladderFam φ hφ _ _ _ P.v 0 P.vpos (Nat.zero_le _) (det_cH_ne (P.s : ℝ) hE hEF _ _ _ hdet) (Mrow hφ P.e P.f P.he0 P.hef) hc
  exact castTF (by simp [vtReg]) (by simp) T

end vtf


section p5f
variable {φ : ℝ} (hφ : 1 < φ) (hφE : φ = (P.f : ℝ) / P.e)

theorem sig5R : (((P.gn - P.e : ℕ) : ℝ)) / (P.gn : ℝ) = sig5 (P.e : ℝ) P.f P.m := by
  have H := P.rh
  have hm := H.hm
  have hg := H.hg1
  have hgmp : 0 < ((P.f : ℝ) - P.e) * P.m := by nlinarith
  rw [Nat.cast_sub P.hge, P.gnR]
  unfold sig5
  have : (0 : ℝ) < P.e := H.hE
  have hme : (P.m : ℝ) ≠ 0 := by linarith
  have hge : ((P.f : ℝ) - P.e) ≠ 0 := by linarith
  field_simp

include hφE

/-- the family of the trapezoid `pi5 = Delta(gn) \ Delta(gn - e)` at `X5 = ((F-E) m, k)` -/
def p5Fam : TFam (Phi φ '' p5Reg (P.e : ℝ) P.f P.m P.j P.s) (Mrow hφ P.e P.f P.he0 P.hef) (P.gn * P.gn - (P.gn - P.e) * (P.gn - P.e)) := by
  have H := P.rh
  obtain ⟨hF, hB, hEF', hv, hm0, hj0⟩ := H.pos
  have hE := H.hE
  have hEF := H.hEF
  have hm := H.hm
  have hg := H.hg1
  have hgmp : 0 < ((P.f : ℝ) - P.e) * P.m := by nlinarith
  have hdet : ((uW (P.e : ℝ) P.f P.m P.j).1 - (uX5 (P.e : ℝ) P.f P.m P.j).1) * ((uU5 (P.e : ℝ) P.f P.m P.j).2 - (uX5 (P.e : ℝ) P.f P.m P.j).2) -
      ((uU5 (P.e : ℝ) P.f P.m P.j).1 - (uX5 (P.e : ℝ) P.f P.m P.j).1) * ((uW (P.e : ℝ) P.f P.m P.j).2 - (uX5 (P.e : ℝ) P.f P.m P.j).2) ≠ 0 := by
    have e1 : ((uW (P.e : ℝ) P.f P.m P.j).1 - (uX5 (P.e : ℝ) P.f P.m P.j).1) * ((uU5 (P.e : ℝ) P.f P.m P.j).2 - (uX5 (P.e : ℝ) P.f P.m P.j).2) -
      ((uU5 (P.e : ℝ) P.f P.m P.j).1 - (uX5 (P.e : ℝ) P.f P.m P.j).1) * ((uW (P.e : ℝ) P.f P.m P.j).2 - (uX5 (P.e : ℝ) P.f P.m P.j).2) =
      ((P.f : ℝ) - P.e) * P.m * ((P.e : ℝ) / P.f) * ((P.f : ℝ) * P.e * P.m / (P.e + P.f)) := by
      simp only [uX5, uW, uU5]; field_simp; ring
    rw [e1]
    have : 0 < ((P.f : ℝ) - P.e) * P.m * ((P.e : ℝ) / P.f) * ((P.f : ℝ) * P.e * P.m / (P.e + P.f)) := by positivity
    exact this.ne'
  have hgn := P.gnR
  have hc := cong_base_apex hφ P.e P.f P.he0 P.hef hφE (P.s : ℝ) (uX5 (P.e : ℝ) P.f P.m P.j) (uW (P.e : ℝ) P.f P.m P.j)
    (uU5 (P.e : ℝ) P.f P.m P.j) P.gn P.gnpos (det_cH_ne (P.s : ℝ) hE hEF _ _ _ hdet) (((P.f : ℝ) ^ 2 - (P.e : ℝ) ^ 2) ^ 2)
    (((P.e : ℝ) * P.f) ^ 2) (((P.f : ℝ) ^ 2) ^ 2)
    (by rw [hgn]; simp only [qf, uX5, uW]; field_simp; ring)
    (by rw [hgn]; simp only [qf, uW, uU5]; field_simp; ring)
    (by rw [hgn]; simp only [qf, uX5, uU5]; field_simp; ring)
    (Or.inl ⟨rfl, rfl, rfl⟩)
  have T := ladderFam φ hφ _ _ _ P.gn (P.gn - P.e) P.gnpos (Nat.sub_le _ _) (det_cH_ne (P.s : ℝ) hE hEF _ _ _ hdet)
    (Mrow hφ P.e P.f P.he0 P.hef) hc
  refine castTF ?_ rfl T
  unfold p5Reg; rw [sig5R]

end p5f


section p4f
variable {φ : ℝ} (hφ : 1 < φ) (hφE : φ = (P.f : ℝ) / P.e)
include hφE

/-- the family of the lattice parallelogram `pi4` (`f` a-steps by `gn` c-steps) hanging from `V2 = (0,t)` -/
def p4Fam : TFam (Phi φ '' p4Reg (P.e : ℝ) P.f P.m P.j P.s) (Mrow hφ P.e P.f P.he0 P.hef) (2 * P.f * P.gn) := by
  have H := P.rh
  obtain ⟨hF, hB, hEF', hv, hm0, hj0⟩ := H.pos
  have hE := H.hE
  have hEF := H.hEF
  have hm := H.hm
  have hdet : ((cH (P.e : ℝ) P.f P.s (uVt P.f P.m P.j) + cHv (P.e : ℝ) P.f (uw1 P.e P.f)).1 - (cH (P.e : ℝ) P.f P.s (uVt P.f P.m P.j)).1) *
      ((cH (P.e : ℝ) P.f P.s (uVt P.f P.m P.j) + cHv (P.e : ℝ) P.f (uw2 P.e P.f)).2 - (cH (P.e : ℝ) P.f P.s (uVt P.f P.m P.j)).2) -
      ((cH (P.e : ℝ) P.f P.s (uVt P.f P.m P.j) + cHv (P.e : ℝ) P.f (uw2 P.e P.f)).1 - (cH (P.e : ℝ) P.f P.s (uVt P.f P.m P.j)).1) *
      ((cH (P.e : ℝ) P.f P.s (uVt P.f P.m P.j) + cHv (P.e : ℝ) P.f (uw1 P.e P.f)).2 - (cH (P.e : ℝ) P.f P.s (uVt P.f P.m P.j)).2) ≠ 0 := by
    have e1 : ((cH (P.e : ℝ) P.f P.s (uVt P.f P.m P.j) + cHv (P.e : ℝ) P.f (uw1 P.e P.f)).1 - (cH (P.e : ℝ) P.f P.s (uVt P.f P.m P.j)).1) *
      ((cH (P.e : ℝ) P.f P.s (uVt P.f P.m P.j) + cHv (P.e : ℝ) P.f (uw2 P.e P.f)).2 - (cH (P.e : ℝ) P.f P.s (uVt P.f P.m P.j)).2) -
      ((cH (P.e : ℝ) P.f P.s (uVt P.f P.m P.j) + cHv (P.e : ℝ) P.f (uw2 P.e P.f)).1 - (cH (P.e : ℝ) P.f P.s (uVt P.f P.m P.j)).1) *
      ((cH (P.e : ℝ) P.f P.s (uVt P.f P.m P.j) + cHv (P.e : ℝ) P.f (uw1 P.e P.f)).2 - (cH (P.e : ℝ) P.f P.s (uVt P.f P.m P.j)).2) =
      (P.f : ℝ) * P.e * ((P.f : ℝ) ^ 2 - (P.e : ℝ) ^ 2) := by
      simp only [cH, cHv, uVt, uw1, uw2, Prod.fst_add, Prod.snd_add]; field_simp; ring
    rw [e1]; positivity
  have hc := cong_cell_apex hφ P.e P.f P.he0 P.hef hφE (P.s : ℝ) (uVt P.f P.m P.j) (uw1 P.e P.f) (uw2 P.e P.f) hdet
    (((P.e : ℝ) * P.f) ^ 2) (((P.f : ℝ) ^ 2 - (P.e : ℝ) ^ 2) ^ 2) (((P.f : ℝ) ^ 2) ^ 2)
    (by simp only [qf, uVt, uw1, Prod.fst_add, Prod.snd_add]; field_simp; ring)
    (by simp only [qf, uVt, uw1, uw2, Prod.fst_add, Prod.snd_add]; field_simp; ring)
    (by simp only [qf, uVt, uw2, Prod.fst_add, Prod.snd_add]; field_simp; ring)
    (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)))
  have T := parFam φ hφ _ _ _ P.f P.gn hdet (Mrow hφ P.e P.f P.he0 P.hef) hc
  refine castTF ?_ rfl T
  unfold p4Reg; rw [P.gnR]

end p4f

end NP

end

end Erdos634.Draft.ThetaNotch
