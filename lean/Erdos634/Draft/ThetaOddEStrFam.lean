-- Draft/ThetaOddEStrFam.lean -- ODD-E formalization, module 2: tile families of the mirrored strips (indices n .. n1-1) for NP4.
-- INTERNAL BUILD ONLY, UNAUDITED beyond internal checks.  No sorry, no native_decide.
/-
Copy of `ThetaNotch3StrFam` for `NP4` (natural `k` instead of `j f`; the real parameter of the regions is `P.jR = k / f`).
The notch construction is the project's (Bonfioli); the first instance `theta_13(3,4)` was found by computer search on 2026-11-15;
the family proof is `internal working notes`.  Credit as in `ThetaNotch3StrFam`: Paliy (band steps on a seed),
Beeson (48-tile seed), Laczkovich, Zhang, Beeson-Rosu (skew frame).  INTERNAL BUILD ONLY, UNAUDITED beyond internal checks.
-/
import Erdos634.Draft.ThetaOddENP

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


def gI (i : ℕ) : ℕ := (P.f - P.e) * i

theorem gIR (i : ℕ) : (P.gI i : ℝ) = ((P.f : ℝ) - P.e) * i := by
  unfold gI; push_cast; rw [Nat.cast_sub P.hef.le]
theorem gI_ge (i : ℕ) (hi : P.n ≤ i) : P.e ≤ P.gI i := by
  unfold gI
  have h1 : P.f - P.e = P.g := by have := P.hfg; omega
  rw [h1]; exact le_trans P.hgn (Nat.mul_le_mul_left _ hi)
theorem gI_pos (i : ℕ) (hi : P.n ≤ i) : 0 < P.gI i := by have := P.gI_ge i hi; have := P.he; omega

theorem sig5Ri (i : ℕ) (hi : P.n ≤ i) : (((P.gI i - P.e : ℕ) : ℝ)) / (P.gI i : ℝ) = sig5b (P.e : ℝ) P.f i := by
  have hge := P.gI_ge i hi
  have hgp := P.gI_pos i hi
  have hgI := P.gIR i
  have H := P.rhR
  have hn : (1 : ℝ) ≤ i := by have : 1 ≤ i := le_trans P.hn hi; exact_mod_cast this
  have hg := H.hg1
  rw [Nat.cast_sub hge, hgI]
  unfold sig5b
  have hge' : ((P.f : ℝ) - P.e) ≠ 0 := by linarith
  have hne : (i : ℝ) ≠ 0 := by linarith
  field_simp

section sf
variable {φ : ℝ} (hφ : 1 < φ) (hφE : φ = (P.f : ℝ) / P.e)
include hφE

/-- the `T` piece of the strip of index `i` -/
def tsFam (i : ℕ) (hi : P.n ≤ i) (hi1 : i ≤ P.n1) : TFam (Phi φ '' tsReg (P.e : ℝ) P.f P.M i P.jR P.s) (Mrow hφ P.e P.f P.he0 P.hef)
    ((P.f + P.gI i) * (P.f + P.gI i) - P.gI i * P.gI i) := by
  have H := P.rhB i hi hi1
  obtain ⟨hF, hB, hEF', hn0, hM, hj0, hv, hen⟩ := H.pos
  have hE := H.hE
  have hEF := H.hEF
  have hgI := P.gIR i
  have hkR : (((P.f + P.gI i : ℕ)) : ℝ) = (P.f : ℝ) + ((P.f : ℝ) - P.e) * i := by push_cast; rw [hgI]
  have hkpos : 0 < P.f + P.gI i := by have := P.gI_pos i hi; omega
  have hdet : ((sO (P.e : ℝ) P.f P.M i P.jR).1 - (sY P.M i P.jR (P.f : ℝ)).1) * ((sU2 (P.e : ℝ) P.f P.M i P.jR).2 - (sY P.M i P.jR (P.f : ℝ)).2) -
      ((sU2 (P.e : ℝ) P.f P.M i P.jR).1 - (sY P.M i P.jR (P.f : ℝ)).1) * ((sO (P.e : ℝ) P.f P.M i P.jR).2 - (sY P.M i P.jR (P.f : ℝ)).2) ≠ 0 := by
    have e1 : ((sO (P.e : ℝ) P.f P.M i P.jR).1 - (sY P.M i P.jR (P.f : ℝ)).1) * ((sU2 (P.e : ℝ) P.f P.M i P.jR).2 - (sY P.M i P.jR (P.f : ℝ)).2) -
      ((sU2 (P.e : ℝ) P.f P.M i P.jR).1 - (sY P.M i P.jR (P.f : ℝ)).1) * ((sO (P.e : ℝ) P.f P.M i P.jR).2 - (sY P.M i P.jR (P.f : ℝ)).2) =
      ((P.f : ℝ) + ((P.f : ℝ) - P.e) * i) ^ 2 / ((P.f : ℝ) ^ 2 - (P.e : ℝ) ^ 2) := by
      simp only [sY, sO, sU2]; field_simp; ring
    rw [e1]
    have : (0 : ℝ) < (P.f : ℝ) + ((P.f : ℝ) - P.e) * i := by nlinarith [H.hg1, H.hn]
    exact div_ne_zero (pow_ne_zero 2 this.ne') hB.ne'
  have hc := cong_base_apex hφ P.e P.f P.he0 P.hef hφE (P.s : ℝ) (sY P.M i P.jR (P.f : ℝ)) (sO (P.e : ℝ) P.f P.M i P.jR)
    (sU2 (P.e : ℝ) P.f P.M i P.jR) (P.f + P.gI i) hkpos (det_cH_ne (P.s : ℝ) hE hEF _ _ _ hdet) (((P.f : ℝ) ^ 2 - (P.e : ℝ) ^ 2) ^ 2)
    (((P.f : ℝ) ^ 2) ^ 2) (((P.e : ℝ) * P.f) ^ 2)
    (by rw [hkR]; simp only [qf, sY, sO]; field_simp; ring)
    (by rw [hkR]; simp only [qf, sO, sU2]; field_simp; ring)
    (by rw [hkR]; simp only [qf, sY, sU2]; field_simp; ring)
    (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))
  have T := ladderFam φ hφ _ _ _ (P.f + P.gI i) (P.gI i) hkpos (Nat.le_add_left _ _) (det_cH_ne (P.s : ℝ) hE hEF _ _ _ hdet)
    (Mrow hφ P.e P.f P.he0 P.hef) hc
  refine castTF ?_ rfl T
  unfold tsReg; rw [hgI, hkR]


/-- the `R` piece of the strip of index `i` (the trapezoid `Delta(g) \ Delta(g - e)` of `pi5`) -/
def rsFam (i : ℕ) (hi : P.n ≤ i) (hi1 : i ≤ P.n1) : TFam (Phi φ '' p52Reg (P.e : ℝ) P.f P.M i P.jR P.s) (Mrow hφ P.e P.f P.he0 P.hef)
    (P.gI i * P.gI i - (P.gI i - P.e) * (P.gI i - P.e)) := by
  have H := P.rhB i hi hi1
  obtain ⟨hF, hB, hEF', hn0, hM, hj0, hv, hen⟩ := H.pos
  have hE := H.hE
  have hEF := H.hEF
  have hg := H.hg1
  have hgI := P.gIR i
  have hdet : ((w2W (P.e : ℝ) P.f P.M i P.jR).1 - (w2X5 P.M i P.jR (P.f : ℝ)).1) * ((w2U5 (P.e : ℝ) P.f P.M i P.jR).2 - (w2X5 P.M i P.jR (P.f : ℝ)).2) -
      ((w2U5 (P.e : ℝ) P.f P.M i P.jR).1 - (w2X5 P.M i P.jR (P.f : ℝ)).1) * ((w2W (P.e : ℝ) P.f P.M i P.jR).2 - (w2X5 P.M i P.jR (P.f : ℝ)).2) ≠ 0 := by
    have e1 : ((w2W (P.e : ℝ) P.f P.M i P.jR).1 - (w2X5 P.M i P.jR (P.f : ℝ)).1) * ((w2U5 (P.e : ℝ) P.f P.M i P.jR).2 - (w2X5 P.M i P.jR (P.f : ℝ)).2) -
      ((w2U5 (P.e : ℝ) P.f P.M i P.jR).1 - (w2X5 P.M i P.jR (P.f : ℝ)).1) * ((w2W (P.e : ℝ) P.f P.M i P.jR).2 - (w2X5 P.M i P.jR (P.f : ℝ)).2) =
      ((P.f : ℝ) - P.e) * (i : ℝ) ^ 2 / ((P.e : ℝ) + P.f) := by
      simp only [w2X5, w2W, w2U5]; field_simp; ring
    rw [e1]
    have : (0 : ℝ) < ((P.f : ℝ) - P.e) * (i : ℝ) ^ 2 / ((P.e : ℝ) + P.f) := by
      have : (0 : ℝ) < i := hn0
      positivity
    exact this.ne'
  have hc := cong_base_apex hφ P.e P.f P.he0 P.hef hφE (P.s : ℝ) (w2X5 P.M i P.jR (P.f : ℝ)) (w2W (P.e : ℝ) P.f P.M i P.jR)
    (w2U5 (P.e : ℝ) P.f P.M i P.jR) (P.gI i) (P.gI_pos i hi) (det_cH_ne (P.s : ℝ) hE hEF _ _ _ hdet) (((P.f : ℝ) ^ 2 - (P.e : ℝ) ^ 2) ^ 2)
    (((P.e : ℝ) * P.f) ^ 2) (((P.f : ℝ) ^ 2) ^ 2)
    (by rw [hgI]; simp only [qf, w2X5, w2W]; field_simp; ring)
    (by rw [hgI]; simp only [qf, w2W, w2U5]; field_simp; ring)
    (by rw [hgI]; simp only [qf, w2X5, w2U5]; field_simp; ring)
    (Or.inl ⟨rfl, rfl, rfl⟩)
  have T := ladderFam φ hφ _ _ _ (P.gI i) (P.gI i - P.e) (P.gI_pos i hi) (Nat.sub_le _ _) (det_cH_ne (P.s : ℝ) hE hEF _ _ _ hdet)
    (Mrow hφ P.e P.f P.he0 P.hef) hc
  refine castTF ?_ rfl T
  unfold p52Reg; rw [P.sig5Ri i hi]

/-- one strip: `T_i u R_i` tile the band, `b (2 i + 1)` tiles -/
def stripFam3 (i : ℕ) (hi : P.n ≤ i) (hi1 : i ≤ P.n1) : TFam (Phi φ '' sbReg (P.e : ℝ) P.f P.M i P.jR P.s) (Mrow hφ P.e P.f P.he0 P.hef)
    (P.b * (2 * i + 1)) := by
  have H := P.rhB i hi hi1
  have hE := H.hE
  have hEF := H.hEF
  obtain ⟨hF, hB, hEF', hn0, hM, hj0, hv, hen⟩ := H.pos
  obtain ⟨a1, a2, a3, a4, a5⟩ := ts_factsB (P.s : ℝ) H
  obtain ⟨b1, b2, b3, b4, b5⟩ := rs_factsB (P.s : ℝ) H
  have hcnt : ((P.f + P.gI i) * (P.f + P.gI i) - P.gI i * P.gI i) + (P.gI i * P.gI i - (P.gI i - P.e) * (P.gI i - P.e)) = P.b * (2 * i + 1) := by
    have := strip_cnt P.e P.f P.b i P.hef P.hb (by have := P.gI_ge i hi; unfold gI at this; exact this)
    unfold gI; exact this
  refine castTF rfl hcnt (TFam.join2 (P.tsFam hφ hφE i hi hi1) (P.rsFam hφ hφE i hi hi1) ?_ ?_ ?_)
  · exact Set.image_mono (fun p hp => ⟨a2 p hp, a3 p hp, a4 p hp, a5 p hp⟩)
  · exact Set.image_mono (fun p hp => ⟨b2 p hp, b3 p hp, b4 p hp, b5 p hp⟩)
  · exact disjoint_image hφ (disjLF (P.s : ℝ) hE hEF (Or.inl one_ne_zero) (by norm_num) (by norm_num) (by norm_num) a1 b1)

end sf

end NP4

end

end Erdos634.Draft.ThetaNotch
