-- Frame f = -c/A, model, cell, and the six region tilings R1..R6 for real (P, g) > 0
-- with the scales supplied as naturals k with real-cast hypotheses.
import Erdos634.Draft.S2GLayout

open scoped Classical
set_option linter.unusedSectionVars false
open Erdos634.Geometry Erdos634.CertCoord
open Erdos634.Draft.CollarParam (Sh Rect RTiling.cast RTiling.castN interior_disj_fst interior_disj_snd)

namespace Erdos634.Draft.S2G
open Erdos634.Draft.WFrameF Erdos634.Draft.RegionTiling Erdos634.Draft.WBrickF
open Erdos634.Draft.BrickGridF (shift_rect)

/-- the NEGATIVE frame parameter `f = -c/A = -(2P+g)/(3P+2g)`. -/
noncomputable def ff (P g : ℝ) : ℝ := -(2 * P + g) / (3 * P + 2 * g)

section real
variable {P g : ℝ} (hP : 0 < P) (hg : 0 < g)
include hP hg

theorem hfr : 1 < 4 * (ff P g) ^ 2 := by
  have hA : 0 < 3 * P + 2 * g := by positivity
  have e : ff P g ^ 2 = (2 * P + g) ^ 2 / (3 * P + 2 * g) ^ 2 := by
    simp only [ff]; rw [neg_div, neg_sq, div_pow]
  rw [e, ← mul_div_assoc, lt_div_iff₀ (by positivity)]
  ppos_lt

theorem Fq (x y : ℝ) : x ^ 2 + y ^ 2 + x * y / ff P g
    = x ^ 2 + y ^ 2 - (3 * P + 2 * g) * x * y / (2 * P + g) := by
  have h1 : (2 * P + g) ≠ 0 := by positivity
  have h2 : (3 * P + 2 * g) ≠ 0 := by positivity
  simp only [ff]; field_simp; ring

theorem hcpos : 0 < 2 * P + g := by positivity
theorem hbpos : 0 < P + g := by positivity

/-- the model tile: lower half of the `[0,c]×[0,b]` cell in the frame `Φ_f`, f = -c/A. -/
noncomputable def Mod : Tri := brickL (ff P g) (hfr hP hg) (2 * P + g) (P + g) (hcpos hP hg) (hbpos hP hg)

theorem hab_id : (2 * P + g) ^ 2 + (P + g) ^ 2 + (2 * P + g) * (P + g) / ff P g = P * (2 * P + g) := by
  have h1 : (2 * P + g) ≠ 0 := by positivity
  have := Fq (P := P) (g := g) hP hg (2 * P + g) (P + g)
  have e : (2 * P + g) ^ 2 + (P + g) ^ 2 + (2 * P + g) * (P + g) / ff P g
      = (2 * P + g) ^ 2 + (P + g) ^ 2 - (3 * P + 2 * g) * (2 * P + g) * (P + g) / (2 * P + g) := by
    have := Fq (P := P) (g := g) hP hg (2 * P + g) (P + g)
    rw [← this]
  rw [e]; field_simp; ring

noncomputable def cellRT : RTiling (Phi (ff P g) '' Rect 0 (2 * P + g) 0 (P + g)) (Mod hP hg) 2 :=
  brick_rt (ff P g) (hfr hP hg) (2 * P + g) (P + g) (hcpos hP hg) (hbpos hP hg) _
    (Tri.Congruent.refl _) (cong_U_cell (hfr hP hg) _ _ _ _)

/-! ### nondegeneracy -/
theorem det1 : ((pO).1 - (pC P g).1) * ((pQ P g).2 - (pC P g).2) - ((pQ P g).1 - (pC P g).1) * ((pO).2 - (pC P g).2) ≠ 0 := by
  have e : ((pO).1 - (pC P g).1) * ((pQ P g).2 - (pC P g).2) - ((pQ P g).1 - (pC P g).1) * ((pO).2 - (pC P g).2)
      = (P + g) * (2 * P + g) ^ 3 := by simp only [pO, pC, pQ]; ring
  rw [e]; positivity
theorem det2 : ((pO).1 - (pP P g).1) * ((pQ P g).2 - (pP P g).2) - ((pQ P g).1 - (pP P g).1) * ((pO).2 - (pP P g).2) ≠ 0 := by
  have e : ((pO).1 - (pP P g).1) * ((pQ P g).2 - (pP P g).2) - ((pQ P g).1 - (pP P g).1) * ((pO).2 - (pP P g).2)
      = -((P + g) * (2 * P + g) ^ 3) := by simp only [pO, pP, pQ]; ring
  rw [e]; exact neg_ne_zero.mpr (by positivity)
theorem det3 : ((pR P g).1 - (pC P g).1) * ((pQ P g).2 - (pC P g).2) - ((pQ P g).1 - (pC P g).1) * ((pR P g).2 - (pC P g).2) ≠ 0 := by
  have e : ((pR P g).1 - (pC P g).1) * ((pQ P g).2 - (pC P g).2) - ((pQ P g).1 - (pC P g).1) * ((pR P g).2 - (pC P g).2)
      = -((P + g) * (2 * P + g) ^ 3) := by simp only [pR, pC, pQ]; ring
  rw [e]; exact neg_ne_zero.mpr (by positivity)
theorem det4 : ((pP P g).1 - (pQ P g).1) * ((pV P g).2 - (pQ P g).2) - ((pV P g).1 - (pQ P g).1) * ((pP P g).2 - (pQ P g).2) ≠ 0 := by
  have e : ((pP P g).1 - (pQ P g).1) * ((pV P g).2 - (pQ P g).2) - ((pV P g).1 - (pQ P g).1) * ((pP P g).2 - (pQ P g).2)
      = P * (P + g) * (2 * P + g) ^ 2 := by simp only [pP, pQ, pV]; ring
  rw [e]; positivity
theorem det5 : ((pW P g).1 - (pV P g).1) * ((pP P g).2 - (pV P g).2) - ((pP P g).1 - (pV P g).1) * ((pW P g).2 - (pV P g).2) ≠ 0 := by
  have e : ((pW P g).1 - (pV P g).1) * ((pP P g).2 - (pV P g).2) - ((pP P g).1 - (pV P g).1) * ((pW P g).2 - (pV P g).2)
      = -((P + g) ^ 3 * (2 * P + g)) := by simp only [pW, pP, pV]; ring
  rw [e]; exact neg_ne_zero.mpr (by positivity)
theorem detT : ((pB P g).1 - (pO).1) * ((pC P g).2 - (pO).2) - ((pC P g).1 - (pO).1) * ((pB P g).2 - (pO).2) ≠ 0 := by
  have e : ((pB P g).1 - (pO).1) * ((pC P g).2 - (pO).2) - ((pC P g).1 - (pO).1) * ((pB P g).2 - (pO).2)
      = (P + g) * (2 * P + g) * (3 * P + 2 * g) * (5 * P + 3 * g) := by simp only [pO, pB, pC]; ring
  rw [e]; positivity

noncomputable def R1 (k : ℕ) (hk0 : 0 < k) (hk : (k : ℝ) = 2 * P + g) :
    RTiling (Phi (ff P g) '' H1 P g) (Mod hP hg) (k * k) :=
  scaledRT (ff P g) (hfr hP hg) (pC P g) pO (pQ P g) k hk0 (det1 hP hg) _
    (baseTri_cong _ _ (2 * P + g) (P + g) (P * (2 * P + g)) (hcpos hP hg) (hbpos hP hg) (hab_id hP hg) _ _ _ k hk0 _
      (by rw [hk]; rw [Fq hP hg]; simp only [pO, pC, pQ]; field_simp; ring)
      (by rw [hk]; rw [Fq hP hg]; simp only [pO, pC, pQ]; field_simp; ring)
      (by rw [hk]; rw [Fq hP hg]; simp only [pO, pC, pQ]; field_simp; ring))

noncomputable def R2 (k : ℕ) (hk0 : 0 < k) (hk : (k : ℝ) = 2 * P + g) :
    RTiling (Phi (ff P g) '' H2 P g) (Mod hP hg) (k * k) :=
  scaledRT (ff P g) (hfr hP hg) (pP P g) pO (pQ P g) k hk0 (det2 hP hg) _
    (baseTri_cong _ _ (2 * P + g) (P + g) (P * (2 * P + g)) (hcpos hP hg) (hbpos hP hg) (hab_id hP hg) _ _ _ k hk0 _
      (by rw [hk]; rw [Fq hP hg]; simp only [pO, pP, pQ]; field_simp; ring)
      (by rw [hk]; rw [Fq hP hg]; simp only [pO, pP, pQ]; field_simp; ring)
      (by rw [hk]; rw [Fq hP hg]; simp only [pO, pP, pQ]; field_simp; ring))

noncomputable def R3 (k : ℕ) (hk0 : 0 < k) (hk : (k : ℝ) = 2 * P + g) :
    RTiling (Phi (ff P g) '' H3 P g) (Mod hP hg) (k * k) :=
  scaledRT (ff P g) (hfr hP hg) (pC P g) (pR P g) (pQ P g) k hk0 (det3 hP hg) _
    (baseTri_cong _ _ (2 * P + g) (P + g) (P * (2 * P + g)) (hcpos hP hg) (hbpos hP hg) (hab_id hP hg) _ _ _ k hk0 _
      (by rw [hk]; rw [Fq hP hg]; simp only [pO, pR, pC, pQ]; field_simp; ring)
      (by rw [hk]; rw [Fq hP hg]; simp only [pO, pR, pC, pQ]; field_simp; ring)
      (by rw [hk]; rw [Fq hP hg]; simp only [pO, pR, pC, pQ]; field_simp; ring))

noncomputable def R4 (k : ℕ) (hk0 : 0 < k) (hk : (k : ℝ) ^ 2 = P * (2 * P + g)) :
    RTiling (Phi (ff P g) '' H4 P g) (Mod hP hg) (k * k) :=
  scaledRT (ff P g) (hfr hP hg) (pQ P g) (pP P g) (pV P g) k hk0 (det4 hP hg) _
    (baseTri_cong _ _ (2 * P + g) (P + g) (P * (2 * P + g)) (hcpos hP hg) (hbpos hP hg) (hab_id hP hg) _ _ _ k hk0 _
      (by rw [mul_pow, hk]; rw [Fq hP hg]; simp only [pP, pQ, pV]; field_simp; ring)
      (by rw [mul_pow, hk]; rw [Fq hP hg]; simp only [pP, pQ, pV]; field_simp; ring)
      (by rw [hk]; rw [Fq hP hg]; simp only [pP, pQ, pV]; field_simp; ring))

noncomputable def R5 (k : ℕ) (hk0 : 0 < k) (hk : (k : ℝ) = P + g) :
    RTiling (Phi (ff P g) '' H5 P g) (Mod hP hg) (k * k) :=
  scaledRT (ff P g) (hfr hP hg) (pV P g) (pW P g) (pP P g) k hk0 (det5 hP hg) _
    (baseTri_cong _ _ (2 * P + g) (P + g) (P * (2 * P + g)) (hcpos hP hg) (hbpos hP hg) (hab_id hP hg) _ _ _ k hk0 _
      (by rw [hk]; rw [Fq hP hg]; simp only [pW, pP, pV]; field_simp; ring)
      (by rw [hk]; rw [Fq hP hg]; simp only [pW, pP, pV]; field_simp; ring)
      (by rw [hk]; rw [Fq hP hg]; simp only [pW, pP, pV]; field_simp; ring))

end real
end Erdos634.Draft.S2G
