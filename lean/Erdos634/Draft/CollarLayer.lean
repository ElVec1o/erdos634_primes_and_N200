-- Draft/CollarLayer.lean — the LAYER STEP of the collar: T_G tiled  ⇒  T_{G+1} tiled, for the base-α isosceles targets of a
-- row (e,f) with e f ≤ f²−e² ("b ≥ a"), tile (a,b,c) = (e f, f²−e², f²), target T_G = (b(b+c)·G, bc·G, bc·G).  UNAUDITED.
-- No sorry, no native_decide.
--
-- Mathematics: the layer lemma of (project working notes) with d = 1, P = b: T_{G+1} is the disjoint union of
--   Mac = translate of T_G by (b², ab) (skew coordinates),  L = Δ(c),  M = Δ(b)\Δ(b−a),  Rt = Δ(b+a')\Δ(a'),  a' = (b+c)G − a.
-- CREDIT: the existence of these α-isosceles families and of an eventual up-set with explicit threshold is Paliy's
-- (docs/eventual-rational-families.md, 2026-09-29; macrodissection of Beeson Thm 24 + gluing); seeds 84, 189: Beeson (v4 Figs 28–29), 189
-- credited to Harries.  What is ours: the collar/layer mechanism with explicit h_max, the parametric seed (Theorem A) and THIS FORMALIZATION
-- (an independent construction; "formalization of Paliy's alpha up-set").  Ingredients: Laczkovich macro-dissections, Beeson–Roșu
-- skew frame S2L, the project's ladder (thm:ladder).
import Erdos634.Draft.CollarLayerLib
import Erdos634.Draft.CollarPts

open scoped Classical
open Erdos634.Geometry Erdos634.CertCoord
open Erdos634.Draft.CollarParam (Sh interior_disj_fst interior_disj_snd)

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Erdos634.Draft.CollarLayer
noncomputable section
open Erdos634.Draft.WFrameF Erdos634.Draft.RegionTiling Erdos634.Draft.WBrickF
open Erdos634.Draft.S2L (baseTri mem_hull3 vol_triC)
open Erdos634.Draft.LadderFam

/-- Membership in the big triangle `T_g = (0,0),(B0 g,0),(b² g, ab g)` as three linear inequalities. -/
def InT (E F g : ℝ) (p : ℝ × ℝ) : Prop :=
  0 ≤ p.2 ∧ 0 ≤ (E*F*(F^2-E^2)*g) * p.1 - ((F^2-E^2)^2*g) * p.2 ∧
    0 ≤ (E*F*(F^2-E^2)*g) * ((pB0 E F)*g - p.1) - ((pB0 E F)*g - (F^2-E^2)^2*g) * p.2

theorem preg_le4 (a V1 V2 q1 q2 : ℝ × ℝ) (σ u w c : ℝ) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (e1x : q1.1 = a.1 + σ * (V1.1 - a.1)) (e1y : q1.2 = a.2 + σ * (V1.2 - a.2))
    (e2x : q2.1 = a.1 + σ * (V2.1 - a.1)) (e2y : q2.2 = a.2 + σ * (V2.2 - a.2))
    (h1 : u * q1.1 + w * q1.2 ≤ c) (h2 : u * q2.1 + w * q2.2 ≤ c) (h3 : u * V1.1 + w * V1.2 ≤ c)
    (h4 : u * V2.1 + w * V2.2 ≤ c) : ∀ p ∈ Preg a V1 V2 σ, u * p.1 + w * p.2 ≤ c :=
  preg_le a V1 V2 σ u w c hσ0 hσ1 (by rw [← e1x, ← e1y]; exact h1) (by rw [← e2x, ← e2y]; exact h2) h3 h4

theorem preg_ge4 (a V1 V2 q1 q2 : ℝ × ℝ) (σ u w c : ℝ) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (e1x : q1.1 = a.1 + σ * (V1.1 - a.1)) (e1y : q1.2 = a.2 + σ * (V1.2 - a.2))
    (e2x : q2.1 = a.1 + σ * (V2.1 - a.1)) (e2y : q2.2 = a.2 + σ * (V2.2 - a.2))
    (h1 : c ≤ u * q1.1 + w * q1.2) (h2 : c ≤ u * q2.1 + w * q2.2) (h3 : c ≤ u * V1.1 + w * V1.2)
    (h4 : c ≤ u * V2.1 + w * V2.2) : ∀ p ∈ Preg a V1 V2 σ, c ≤ u * p.1 + w * p.2 :=
  preg_ge a V1 V2 σ u w c hσ0 hσ1 (by rw [← e1x, ← e1y]; exact h1) (by rw [← e2x, ← e2y]; exact h2) h3 h4

theorem preg_inT (E F g : ℝ) (a V1 V2 q1 q2 : ℝ × ℝ) (σ : ℝ) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (e1x : q1.1 = a.1 + σ * (V1.1 - a.1)) (e1y : q1.2 = a.2 + σ * (V1.2 - a.2))
    (e2x : q2.1 = a.1 + σ * (V2.1 - a.1)) (e2y : q2.2 = a.2 + σ * (V2.2 - a.2))
    (h1 : InT E F g q1) (h2 : InT E F g q2) (h3 : InT E F g V1) (h4 : InT E F g V2) :
    ∀ p ∈ Preg a V1 V2 σ, InT E F g p := by
  intro p hp
  refine ⟨?_, ?_, ?_⟩
  · have := preg_ge4 a V1 V2 q1 q2 σ 0 1 0 hσ0 hσ1 e1x e1y e2x e2y (by linarith [h1.1]) (by linarith [h2.1])
      (by linarith [h3.1]) (by linarith [h4.1]) p hp
    linarith
  · have := preg_ge4 a V1 V2 q1 q2 σ (E*F*(F^2-E^2)*g) (-((F^2-E^2)^2*g)) 0 hσ0 hσ1 e1x e1y e2x e2y
      (by linarith [h1.2.1]) (by linarith [h2.2.1]) (by linarith [h3.2.1]) (by linarith [h4.2.1]) p hp
    linarith
  · have := preg_ge4 a V1 V2 q1 q2 σ (-(E*F*(F^2-E^2)*g)) (-((pB0 E F)*g - (F^2-E^2)^2*g))
      (-(E*F*(F^2-E^2)*g) * (pB0 E F * g)) hσ0 hσ1 e1x e1y e2x e2y
      (by nlinarith [h1.2.2]) (by nlinarith [h2.2.2]) (by nlinarith [h3.2.2]) (by nlinarith [h4.2.2]) p hp
    nlinarith

theorem inT_mem (E F g : ℝ) (hE : 0 < E) (hEF : E < F) (hg : 0 < g) (hba : E * F ≤ F ^ 2 - E ^ 2)
    {p : ℝ × ℝ} (h : InT E F g p) :
    p ∈ convexHull ℝ ({((0 : ℝ), (0 : ℝ)), (pB0 E F * g, 0), ((F^2-E^2)^2 * g, E*F*(F^2-E^2) * g)} : Set (ℝ × ℝ)) := by
  have hb : 0 < F^2 - E^2 := by nlinarith
  have hB : 0 < pB0 E F * g := by unfold pB0; have : 0 < F^2 := by nlinarith
                                  positivity
  have hy : 0 < E*F*(F^2-E^2) * g := by have : 0 < F := by linarith
                                        positivity
  obtain ⟨h1, h2, h3⟩ := h
  have := mem_tri_iso (B := pB0 E F * g) (xA := (F^2-E^2)^2 * g) (yA := E*F*(F^2-E^2) * g) (X := p.1) (Y := p.2)
    hB hy h1 h2 h3
  simpa using this


section pts
variable (E F G : ℝ) (hE : 0 < E) (hEF : E < F) (hG : 1 ≤ G) (hba : E * F ≤ F ^ 2 - E ^ 2)
include hE hEF hG hba

theorem inT_O : InT E F (G+1) (pO E F) := ⟨pt_inT0_O E F G hE hEF hG hba, pt_inT1_O E F G hE hEF hG hba, pt_inT2_O E F G hE hEF hG hba⟩
theorem inT_P1 : InT E F (G+1) (pP1 E F) := ⟨pt_inT0_P1 E F G hE hEF hG hba, pt_inT1_P1 E F G hE hEF hG hba, pt_inT2_P1 E F G hE hEF hG hba⟩
theorem inT_C0 : InT E F (G+1) (pC0 E F) := ⟨pt_inT0_C0 E F G hE hEF hG hba, pt_inT1_C0 E F G hE hEF hG hba, pt_inT2_C0 E F G hE hEF hG hba⟩
theorem inT_BL : InT E F (G+1) (pBL E F) := ⟨pt_inT0_BL E F G hE hEF hG hba, pt_inT1_BL E F G hE hEF hG hba, pt_inT2_BL E F G hE hEF hG hba⟩
theorem inT_TR : InT E F (G+1) (pTR E F) := ⟨pt_inT0_TR E F G hE hEF hG hba, pt_inT1_TR E F G hE hEF hG hba, pt_inT2_TR E F G hE hEF hG hba⟩
theorem inT_E : InT E F (G+1) (pE E F (G+1)) := ⟨pt_inT0_E E F G hE hEF hG hba, pt_inT1_E E F G hE hEF hG hba, pt_inT2_E E F G hE hEF hG hba⟩
theorem inT_TRR : InT E F (G+1) (pTRR E F (G+1)) := ⟨pt_inT0_TRR E F G hE hEF hG hba, pt_inT1_TRR E F G hE hEF hG hba, pt_inT2_TRR E F G hE hEF hG hba⟩
end pts

/-! ### The three trapezoid pieces -/

section pieces
theorem pos_facts {E F : ℝ} (hE : 0 < E) (hEF : E < F) : 0 < F ^ 2 - E ^ 2 ∧ 0 < E * F ∧ 0 < F ^ 2 := by
  have : 0 < F := by linarith
  refine ⟨by nlinarith, by positivity, by positivity⟩

variable {φ : ℝ} (hφ : 1 < φ) {E F : ℝ} (hE : 0 < E) (hEF : E < F)
include hE hEF

/-- Piece `L = Δ(c)`: apex `(0,0)`, `V1 = (b², ab)`, `V2 = (c², 0)`, scale `kc = c`. -/
theorem cong_L (hφE : φ = F / E) {kc : ℕ} (hk : 0 < kc) (hkc : (kc : ℝ) = F ^ 2)
    (hdet : ((pP1 E F).1 - (pO E F).1) * ((pC0 E F).2 - (pO E F).2) - ((pC0 E F).1 - (pO E F).1) * ((pP1 E F).2 - (pO E F).2) ≠ 0)
    (hA : 0 < F ^ 2 - E ^ 2) (hB : 0 < E * F) :
    (baseTri φ hφ (pO E F) (pP1 E F) (pC0 E F) kc hk hdet).Congruent (brickL φ hφ (F ^ 2 - E ^ 2) (E * F) hA hB) := by
  have hF : 0 < F := by linarith
  have hE0 : E ≠ 0 := hE.ne'
  have hF0 : F ≠ 0 := hF.ne'
  have hb0 : F ^ 2 - E ^ 2 ≠ 0 := hA.ne'
  subst hφE
  refine Erdos634.SssCongruent.congruent_of_dist_three ?_ ?_ ?_ <;>
    simp only [baseTri, brickL, triC_pts] <;>
    (refine dPhi _ _ _ _ ?_; rw [sq_Phi hφ, sq_Phi hφ];
     simp only [pO, pP1, pC0, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, Prod.fst_sub,
       Prod.snd_sub, hkc]
     field_simp; ring)

theorem det_L : ((pP1 E F).1 - (pO E F).1) * ((pC0 E F).2 - (pO E F).2) - ((pC0 E F).1 - (pO E F).1) * ((pP1 E F).2 - (pO E F).2) ≠ 0 := by
  obtain ⟨hb, ha, hc⟩ := pos_facts hE hEF
  have : ((pP1 E F).1 - (pO E F).1) * ((pC0 E F).2 - (pO E F).2) - ((pC0 E F).1 - (pO E F).1) * ((pP1 E F).2 - (pO E F).2)
      = -((F^2)^2 * (E*F*(F^2-E^2))) := by simp only [pO, pP1, pC0]; ring
  rw [this]
  exact neg_ne_zero.mpr (mul_pos (pow_pos hc 2) (mul_pos ha hb)).ne'

theorem det_M : ((pTR E F).1 - (pQ E F).1) * ((pP1 E F).2 - (pQ E F).2) - ((pP1 E F).1 - (pQ E F).1) * ((pTR E F).2 - (pQ E F).2) ≠ 0 := by
  obtain ⟨hb, ha, hc⟩ := pos_facts hE hEF
  have : ((pTR E F).1 - (pQ E F).1) * ((pP1 E F).2 - (pQ E F).2) - ((pP1 E F).1 - (pQ E F).1) * ((pTR E F).2 - (pQ E F).2)
      = (F^2-E^2)^2 * (E*F*(F^2-E^2)) := by simp only [pQ, pTR, pP1]; ring
  rw [this]
  exact (mul_pos (pow_pos hb 2) (mul_pos ha hb)).ne'

theorem cong_M (hφE : φ = F / E) {kb : ℕ} (hk : 0 < kb) (hkb : (kb : ℝ) = F ^ 2 - E ^ 2) :
    (baseTri φ hφ (pQ E F) (pTR E F) (pP1 E F) kb hk (det_M hE hEF)).Congruent
      (brickL φ hφ (F ^ 2 - E ^ 2) (E * F) (pos_facts hE hEF).1 (pos_facts hE hEF).2.1) := by
  have hF : 0 < F := by linarith
  have hE0 : E ≠ 0 := hE.ne'
  have hF0 : F ≠ 0 := hF.ne'
  have hb0 : F ^ 2 - E ^ 2 ≠ 0 := (pos_facts hE hEF).1.ne'
  subst hφE
  refine Erdos634.SssCongruent.congruent_of_dist_three ?_ ?_ ?_ <;>
    simp only [baseTri, brickL, triC_pts] <;>
    (refine dPhi _ _ _ _ ?_; rw [sq_Phi hφ, sq_Phi hφ];
     simp only [pQ, pTR, pP1, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, Prod.fst_sub,
       Prod.snd_sub, hkb]
     field_simp; ring)

section rt
variable (G ap : ℝ) (hG : 1 ≤ G) (hap : ap = (F ^ 2 - E ^ 2 + F ^ 2) * G - E * F) (hba : E * F ≤ F ^ 2 - E ^ 2)
include hG hap hba

theorem S_pos : 0 < (F ^ 2 - E ^ 2) + ap := by
  obtain ⟨hb, ha, hc⟩ := pos_facts hE hEF
  subst hap
  nlinarith

theorem det_R : ((pBL E F).1 - (pR E F ap).1) * ((pE E F (G+1)).2 - (pR E F ap).2) - ((pE E F (G+1)).1 - (pR E F ap).1) * ((pBL E F).2 - (pR E F ap).2) ≠ 0 := by
  obtain ⟨hb, ha, hc⟩ := pos_facts hE hEF
  have hS := S_pos hE hEF G ap hG hap hba
  have : ((pBL E F).1 - (pR E F ap).1) * ((pE E F (G+1)).2 - (pR E F ap).2) - ((pE E F (G+1)).1 - (pR E F ap).1) * ((pBL E F).2 - (pR E F ap).2)
      = (E*F) * (F^2-E^2) * ((F^2-E^2) + ap)^2 := by
    subst hap; simp only [pBL, pR, pE, pB0]; ring
  rw [this]
  exact (mul_pos (mul_pos ha hb) (pow_pos hS 2)).ne'

theorem cong_R (hφE : φ = F / E) {kS : ℕ} (hk : 0 < kS) (hkS : (kS : ℝ) = (F ^ 2 - E ^ 2) + ap) :
    (baseTri φ hφ (pR E F ap) (pBL E F) (pE E F (G+1)) kS hk (det_R hE hEF G ap hG hap hba)).Congruent
      (brickU φ hφ (F ^ 2 - E ^ 2) (E * F) (pos_facts hE hEF).1 (pos_facts hE hEF).2.1) := by
  have hF : 0 < F := by linarith
  have hE0 : E ≠ 0 := hE.ne'
  have hF0 : F ≠ 0 := hF.ne'
  have hS := (S_pos hE hEF G ap hG hap hba).ne'
  have hEx : (pE E F (G+1)).1 = (pBL E F).1 + (F^2-E^2) * ((F^2-E^2) + ap) := by
    subst hap; simp only [pE, pB0, pBL]; ring
  have hE2 : (pE E F (G+1)).2 = 0 := rfl
  subst hφE
  refine Erdos634.SssCongruent.congruent_of_dist_three ?_ ?_ ?_ <;>
    simp only [baseTri, brickU, triC_pts] <;>
    (refine dPhi _ _ _ _ ?_; rw [sq_Phi hφ, sq_Phi hφ];
     simp only [pR, pBL, hEx, hE2, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, Prod.fst_sub,
       Prod.snd_sub, hkS]
     field_simp; ring)


end rt

/-- Equations for the cut vertices of `M`. -/
theorem eq_M {kb spM : ℕ} (hkb : (kb : ℝ) = F ^ 2 - E ^ 2) (hsp : (spM : ℝ) = F ^ 2 - E ^ 2 - E * F) :
    (pBL E F).1 = (pQ E F).1 + ((spM : ℝ) / kb) * ((pTR E F).1 - (pQ E F).1) ∧
    (pBL E F).2 = (pQ E F).2 + ((spM : ℝ) / kb) * ((pTR E F).2 - (pQ E F).2) ∧
    (pC0 E F).1 = (pQ E F).1 + ((spM : ℝ) / kb) * ((pP1 E F).1 - (pQ E F).1) ∧
    (pC0 E F).2 = (pQ E F).2 + ((spM : ℝ) / kb) * ((pP1 E F).2 - (pQ E F).2) := by
  obtain ⟨hb, ha, hc⟩ := pos_facts hE hEF
  have hF : 0 < F := by linarith
  have hb0 : F ^ 2 - E ^ 2 ≠ 0 := hb.ne'
  have hE0 := hE.ne'
  have hF0 := hF.ne'
  rw [hkb, hsp]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [pBL, pC0, pQ, pTR, pP1] <;> field_simp <;> ring

theorem eq_R (G ap : ℝ) (hap : ap = (F ^ 2 - E ^ 2 + F ^ 2) * G - E * F) {kS apn : ℕ}
    (hkS : (kS : ℝ) = (F ^ 2 - E ^ 2) + ap) (hapn : (apn : ℝ) = ap) (hS : (F ^ 2 - E ^ 2) + ap ≠ 0) :
    (pTR E F).1 = (pR E F ap).1 + ((apn : ℝ) / kS) * ((pBL E F).1 - (pR E F ap).1) ∧
    (pTR E F).2 = (pR E F ap).2 + ((apn : ℝ) / kS) * ((pBL E F).2 - (pR E F ap).2) ∧
    (pTRR E F (G+1)).1 = (pR E F ap).1 + ((apn : ℝ) / kS) * ((pE E F (G+1)).1 - (pR E F ap).1) ∧
    (pTRR E F (G+1)).2 = (pR E F ap).2 + ((apn : ℝ) / kS) * ((pE E F (G+1)).2 - (pR E F ap).2) := by
  have hEx : (pE E F (G+1)).1 = (pBL E F).1 + (F^2-E^2) * ((F^2-E^2) + ap) := by
    subst hap; simp only [pE, pB0, pBL]; ring
  have hT : (pTRR E F (G+1)).1 = (pBL E F).1 + (F^2-E^2) * ((F^2-E^2) + ap) - (F^2-E^2) * F^2 := by
    subst hap; simp only [pTRR, pB0, pBL]; ring
  rw [hkS, hapn, hEx, hT]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [pBL, pR, pTR, pTRR, pE] <;> field_simp <;> ring

end pieces

/-! ### Assembly of the layer step -/

/-- The big triangle region `T_g` (in the frame `Φ_φ`). -/
def TG (φ E F g : ℝ) : Set Plane :=
  Phi φ '' convexHull ℝ ({((0 : ℝ), (0 : ℝ)), (pB0 E F * g, 0), ((F^2-E^2)^2 * g, E*F*(F^2-E^2) * g)} : Set (ℝ × ℝ))

theorem inT_A (E F G : ℝ) (hE : 0 < E) (hEF : E < F) (hG : 1 ≤ G) :
    InT E F (G+1) ((F^2-E^2)^2 * (G+1), E*F*(F^2-E^2) * (G+1)) := by
  obtain ⟨hb, ha, hc⟩ := pos_facts hE hEF
  refine ⟨?_, le_of_eq (by simp only []; ring), le_of_eq (by simp only []; unfold pB0; ring)⟩
  have : 0 < G + 1 := by linarith
  exact (mul_pos (mul_pos ha hb) this).le

theorem mac_inT (E F G : ℝ) (hE : 0 < E) (hEF : E < F) (hG : 1 ≤ G) (hba : E * F ≤ F ^ 2 - E ^ 2) :
    ∀ p ∈ Sh (pP1 E F) (convexHull ℝ ({((0 : ℝ), (0 : ℝ)), (pB0 E F * G, 0), ((F^2-E^2)^2 * G, E*F*(F^2-E^2) * G)} : Set (ℝ × ℝ))),
      InT E F (G+1) p ∧ (E*F*(F^2-E^2)) ≤ p.2 := by
  intro p hp
  have hp' : p - pP1 E F ∈ convexHull ℝ ({((0 : ℝ), (0 : ℝ)), (pB0 E F * G, 0), ((F^2-E^2)^2 * G, E*F*(F^2-E^2) * G)} : Set (ℝ × ℝ)) := hp
  obtain ⟨hb, ha, hc⟩ := pos_facts hE hEF
  have hG0 : 0 ≤ G := by linarith
  have hB0 : 0 ≤ pB0 E F := by unfold pB0; have : 0 < F^2 := hc; positivity
  have vO := inT_P1 E F G hE hEF hG hba
  have vE := inT_TRR E F G hE hEF hG hba
  have vA := inT_A E F G hE hEF hG
  unfold InT at vO vE vA
  dsimp only [pP1, pTRR] at vO vE
  set q := p - pP1 E F with hq
  have hq1 : p.1 = q.1 + (F^2-E^2)^2 := by simp [hq, pP1]
  have hq2 : p.2 = q.2 + E*F*(F^2-E^2) := by simp [hq, pP1]
  have Y0 := Erdos634.Draft.S2L.hull_ge 0 1 0 (S := ({((0 : ℝ), (0 : ℝ)), (pB0 E F * G, 0), ((F^2-E^2)^2 * G, E*F*(F^2-E^2) * G)} : Set (ℝ × ℝ)))
    (by intro v hv; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
        rcases hv with rfl | rfl | rfl
        · simp
        · simp
        · simp only []; have := mul_nonneg (mul_nonneg ha.le hb.le) hG0; nlinarith) q hp'
  have C2 := Erdos634.Draft.S2L.hull_ge (E*F*(F^2-E^2)*(G+1)) (-((F^2-E^2)^2*(G+1))) 0
    (S := ({((0 : ℝ), (0 : ℝ)), (pB0 E F * G, 0), ((F^2-E^2)^2 * G, E*F*(F^2-E^2) * G)} : Set (ℝ × ℝ)))
    (by intro v hv; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
        rcases hv with rfl | rfl | rfl
        · simp
        · simp only []; unfold pB0
          have : 0 ≤ E*F*(F^2-E^2)*(G+1) * ((F^2-E^2)*((F^2-E^2)+F^2)*G) := by
            have : 0 < G + 1 := by linarith
            have h2 : 0 ≤ (F^2-E^2)*((F^2-E^2)+F^2)*G := by positivity
            exact mul_nonneg (mul_pos (mul_pos ha hb) this).le h2
          nlinarith
        · simp only []; nlinarith) q hp'
  have C3 := Erdos634.Draft.S2L.hull_ge (-(E*F*(F^2-E^2)*(G+1))) (-((pB0 E F*(G+1) - (F^2-E^2)^2*(G+1))))
    (-((E*F*(F^2-E^2)*(G+1)) * (pB0 E F*(G+1) - (F^2-E^2)^2) - (pB0 E F*(G+1) - (F^2-E^2)^2*(G+1)) * (E*F*(F^2-E^2))))
    (S := ({((0 : ℝ), (0 : ℝ)), (pB0 E F * G, 0), ((F^2-E^2)^2 * G, E*F*(F^2-E^2) * G)} : Set (ℝ × ℝ)))
    (by intro v hv; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
        rcases hv with rfl | rfl | rfl
        · simp only []; nlinarith [vO.2.2]
        · simp only []; nlinarith [vE.2.2]
        · simp only []; nlinarith [vA.2.2]) q hp'
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · rw [hq2]; linarith
  · rw [hq1, hq2]; nlinarith
  · rw [hq1, hq2]; nlinarith
  · rw [hq2]; linarith

open MeasureTheory in
/-- **The layer step, real-level core.**  Naturals `kc kb spM apn N0` are the ladder scales and the tile count; the hypotheses
`hkc … hN0` say they equal `c, b, b−a, a', b(b+c)` with `a = E F`, `b = F²−E²`, `c = F²`, `a' = (b+c)G − a`. -/
theorem layer_core {φ E F : ℝ} (hφ : 1 < φ) (hφE : φ = F / E) (hE : 0 < E) (hEF : E < F)
    (hba : E * F ≤ F ^ 2 - E ^ 2) (G : ℕ) (hG : 1 ≤ G) (kc kb spM apn N0 : ℕ)
    (hkc : (kc : ℝ) = F ^ 2) (hkb : (kb : ℝ) = F ^ 2 - E ^ 2) (hsp : (spM : ℝ) = F ^ 2 - E ^ 2 - E * F)
    (hap : (apn : ℝ) = (F ^ 2 - E ^ 2 + F ^ 2) * G - E * F) (hN0 : (N0 : ℝ) = (F ^ 2 - E ^ 2) * ((F ^ 2 - E ^ 2) + F ^ 2))
    (R : RTiling (TG φ E F (G : ℝ)) (brickL φ hφ (F ^ 2 - E ^ 2) (E * F) (pos_facts hE hEF).1 (pos_facts hE hEF).2.1) (N0 * G * G)) :
    Nonempty (RTiling (TG φ E F ((G : ℝ) + 1)) (brickL φ hφ (F ^ 2 - E ^ 2) (E * F) (pos_facts hE hEF).1 (pos_facts hE hEF).2.1)
      (N0 * (G + 1) * (G + 1))) := by
  obtain ⟨hb, ha, hc⟩ := pos_facts hE hEF
  have hF : 0 < F := by linarith
  have hGr : (1 : ℝ) ≤ G := by exact_mod_cast hG
  set M := brickL φ hφ (F ^ 2 - E ^ 2) (E * F) hb ha with hMdef
  have hkcpos : 0 < kc := by
    have : (0 : ℝ) < kc := by rw [hkc]; exact hc
    exact_mod_cast this
  have hkbpos : 0 < kb := by
    have : (0 : ℝ) < kb := by rw [hkb]; exact hb
    exact_mod_cast this
  have hspk : spM ≤ kb := by
    have : (spM : ℝ) ≤ kb := by rw [hsp, hkb]; linarith
    exact_mod_cast this
  have hkS : ((kb + apn : ℕ) : ℝ) = (F ^ 2 - E ^ 2) + (apn : ℝ) := by push_cast; rw [hkb]
  have hS := S_pos hE hEF (G : ℝ) (apn : ℝ) hGr hap hba
  have hkSpos : 0 < kb + apn := Nat.add_pos_left hkbpos _
  have hapk : apn ≤ kb + apn := Nat.le_add_left _ _
  -- the four tile families
  let famL : TFam (Phi φ '' Preg (pO E F) (pP1 E F) (pC0 E F) (((0 : ℕ) : ℝ) / (kc : ℝ))) M (kc * kc - 0 * 0) :=
    ladderFam φ hφ (pO E F) (pP1 E F) (pC0 E F) kc 0 hkcpos (Nat.zero_le _) (det_L hE hEF) M
      (cong_L hφ hE hEF hφE hkcpos hkc (det_L hE hEF) hb ha)
  let famM : TFam (Phi φ '' Preg (pQ E F) (pTR E F) (pP1 E F) ((spM : ℝ) / (kb : ℝ))) M (kb * kb - spM * spM) :=
    ladderFam φ hφ (pQ E F) (pTR E F) (pP1 E F) kb spM hkbpos hspk (det_M hE hEF) M
      (cong_M hφ hE hEF hφE hkbpos hkb)
  let famR : TFam (Phi φ '' Preg (pR E F (apn : ℝ)) (pBL E F) (pE E F ((G : ℝ) + 1)) ((apn : ℝ) / ((kb + apn : ℕ) : ℝ)))
      M ((kb + apn) * (kb + apn) - apn * apn) :=
    TFam.remodel (ladderFam φ hφ (pR E F (apn : ℝ)) (pBL E F) (pE E F ((G : ℝ) + 1)) (kb + apn) apn hkSpos hapk
      (det_R hE hEF (G : ℝ) (apn : ℝ) hGr hap hba) (brickU φ hφ (F ^ 2 - E ^ 2) (E * F) hb ha)
      (cong_R hφ hE hEF (G : ℝ) (apn : ℝ) hGr hap hba hφE hkSpos hkS)) (brickU_cong_brickL hφ _ _ hb ha)
  let H : Set (ℝ × ℝ) := convexHull ℝ ({((0 : ℝ), (0 : ℝ)), (pB0 E F * (G : ℝ), 0),
    ((F ^ 2 - E ^ 2) ^ 2 * (G : ℝ), E * F * (F ^ 2 - E ^ 2) * (G : ℝ))} : Set (ℝ × ℝ))
  let famMac : TFam (Phi φ '' Sh (pP1 E F) H) M (N0 * G * G) := TFam.ofR (shiftR (S := H) R (pP1 E F))
  -- σ ranges and the cut-vertex equations
  have hσ0L : (0 : ℝ) ≤ ((0 : ℕ) : ℝ) / (kc : ℝ) := by simp
  have hσ1L : ((0 : ℕ) : ℝ) / (kc : ℝ) ≤ 1 := by simp
  have hσ0M : (0 : ℝ) ≤ (spM : ℝ) / (kb : ℝ) := by positivity
  have hσ1M : (spM : ℝ) / (kb : ℝ) ≤ 1 := by
    rw [div_le_one (by exact_mod_cast hkbpos)]; exact_mod_cast hspk
  have hσ0R : (0 : ℝ) ≤ (apn : ℝ) / ((kb + apn : ℕ) : ℝ) := by positivity
  have hσ1R : (apn : ℝ) / ((kb + apn : ℕ) : ℝ) ≤ 1 := by
    rw [div_le_one (by exact_mod_cast hkSpos)]; exact_mod_cast hapk
  have eL : ∀ q : ℝ × ℝ, q = pO E F → q.1 = (pO E F).1 + (((0 : ℕ) : ℝ) / (kc : ℝ)) * ((pP1 E F).1 - (pO E F).1) ∧
      q.2 = (pO E F).2 + (((0 : ℕ) : ℝ) / (kc : ℝ)) * ((pP1 E F).2 - (pO E F).2) := by
    rintro q rfl; simp
  have eL2 : ∀ q : ℝ × ℝ, q = pO E F → q.1 = (pO E F).1 + (((0 : ℕ) : ℝ) / (kc : ℝ)) * ((pC0 E F).1 - (pO E F).1) ∧
      q.2 = (pO E F).2 + (((0 : ℕ) : ℝ) / (kc : ℝ)) * ((pC0 E F).2 - (pO E F).2) := by
    rintro q rfl; simp
  obtain ⟨m1x, m1y, m2x, m2y⟩ := eq_M hE hEF hkb hsp
  obtain ⟨r1x, r1y, r2x, r2y⟩ := eq_R hE hEF (G : ℝ) (apn : ℝ) hap hkS rfl hS.ne'
  have l1le_L : ∀ p ∈ Preg (pO E F) (pP1 E F) (pC0 E F) (((0 : ℕ) : ℝ) / (kc : ℝ)), (E*F*(F^2-E^2)) * p.1 + ((F^2)^2-(F^2-E^2)^2) * p.2 ≤ (E*F*(F^2-E^2))*((F^2)^2) :=
    preg_le4 _ _ _ (pO E F) (pO E F) _ _ _ _ hσ0L hσ1L (eL _ rfl).1 (eL _ rfl).2 (eL2 _ rfl).1 (eL2 _ rfl).2 (pt_l1le_O E F (G:ℝ) hE hEF hGr hba) (pt_l1le_O E F (G:ℝ) hE hEF hGr hba) (pt_l1le_P1 E F (G:ℝ) hE hEF hGr hba) (pt_l1le_C0 E F (G:ℝ) hE hEF hGr hba)
  have Yle_L : ∀ p ∈ Preg (pO E F) (pP1 E F) (pC0 E F) (((0 : ℕ) : ℝ) / (kc : ℝ)), 0 * p.1 + 1 * p.2 ≤ (E*F*(F^2-E^2)) :=
    preg_le4 _ _ _ (pO E F) (pO E F) _ _ _ _ hσ0L hσ1L (eL _ rfl).1 (eL _ rfl).2 (eL2 _ rfl).1 (eL2 _ rfl).2 (pt_Yle_O E F (G:ℝ) hE hEF hGr hba) (pt_Yle_O E F (G:ℝ) hE hEF hGr hba) (pt_Yle_P1 E F (G:ℝ) hE hEF hGr hba) (pt_Yle_C0 E F (G:ℝ) hE hEF hGr hba)
  have l1ge_M : ∀ p ∈ Preg (pQ E F) (pTR E F) (pP1 E F) ((spM : ℝ) / (kb : ℝ)), (E*F*(F^2-E^2))*((F^2)^2) ≤ (E*F*(F^2-E^2)) * p.1 + ((F^2)^2-(F^2-E^2)^2) * p.2 :=
    preg_ge4 _ _ _ (pBL E F) (pC0 E F) _ _ _ _ hσ0M hσ1M m1x m1y m2x m2y (pt_l1ge_BL E F (G:ℝ) hE hEF hGr hba) (pt_l1ge_C0 E F (G:ℝ) hE hEF hGr hba) (pt_l1ge_TR E F (G:ℝ) hE hEF hGr hba) (pt_l1ge_P1 E F (G:ℝ) hE hEF hGr hba)
  have Yle_M : ∀ p ∈ Preg (pQ E F) (pTR E F) (pP1 E F) ((spM : ℝ) / (kb : ℝ)), 0 * p.1 + 1 * p.2 ≤ (E*F*(F^2-E^2)) :=
    preg_le4 _ _ _ (pBL E F) (pC0 E F) _ _ _ _ hσ0M hσ1M m1x m1y m2x m2y (pt_Yle_BL E F (G:ℝ) hE hEF hGr hba) (pt_Yle_C0 E F (G:ℝ) hE hEF hGr hba) (pt_Yle_TR E F (G:ℝ) hE hEF hGr hba) (pt_Yle_P1 E F (G:ℝ) hE hEF hGr hba)
  have l1ge_R : ∀ p ∈ Preg (pR E F (apn : ℝ)) (pBL E F) (pE E F ((G:ℝ)+1)) ((apn : ℝ) / ((kb + apn : ℕ) : ℝ)), (E*F*(F^2-E^2))*((F^2)^2) ≤ (E*F*(F^2-E^2)) * p.1 + ((F^2)^2-(F^2-E^2)^2) * p.2 :=
    preg_ge4 _ _ _ (pTR E F) (pTRR E F ((G:ℝ)+1)) _ _ _ _ hσ0R hσ1R r1x r1y r2x r2y (pt_l1ge_TR E F (G:ℝ) hE hEF hGr hba) (pt_l1ge_TRR E F (G:ℝ) hE hEF hGr hba) (pt_l1ge_BL E F (G:ℝ) hE hEF hGr hba) (pt_l1ge_E E F (G:ℝ) hE hEF hGr hba)
  have Yle_R : ∀ p ∈ Preg (pR E F (apn : ℝ)) (pBL E F) (pE E F ((G:ℝ)+1)) ((apn : ℝ) / ((kb + apn : ℕ) : ℝ)), 0 * p.1 + 1 * p.2 ≤ (E*F*(F^2-E^2)) :=
    preg_le4 _ _ _ (pTR E F) (pTRR E F ((G:ℝ)+1)) _ _ _ _ hσ0R hσ1R r1x r1y r2x r2y (pt_Yle_TR E F (G:ℝ) hE hEF hGr hba) (pt_Yle_TRR E F (G:ℝ) hE hEF hGr hba) (pt_Yle_BL E F (G:ℝ) hE hEF hGr hba) (pt_Yle_E E F (G:ℝ) hE hEF hGr hba)
  have l2le_M : ∀ p ∈ Preg (pQ E F) (pTR E F) (pP1 E F) ((spM : ℝ) / (kb : ℝ)), (E*F) * p.1 + (F^2-(F^2-E^2)) * p.2 ≤ (E*F*(F^2-E^2))*(E*F+F^2) :=
    preg_le4 _ _ _ (pBL E F) (pC0 E F) _ _ _ _ hσ0M hσ1M m1x m1y m2x m2y (pt_l2le_BL E F (G:ℝ) hE hEF hGr hba) (pt_l2le_C0 E F (G:ℝ) hE hEF hGr hba) (pt_l2le_TR E F (G:ℝ) hE hEF hGr hba) (pt_l2le_P1 E F (G:ℝ) hE hEF hGr hba)
  have l2ge_R : ∀ p ∈ Preg (pR E F (apn : ℝ)) (pBL E F) (pE E F ((G:ℝ)+1)) ((apn : ℝ) / ((kb + apn : ℕ) : ℝ)), (E*F*(F^2-E^2))*(E*F+F^2) ≤ (E*F) * p.1 + (F^2-(F^2-E^2)) * p.2 :=
    preg_ge4 _ _ _ (pTR E F) (pTRR E F ((G:ℝ)+1)) _ _ _ _ hσ0R hσ1R r1x r1y r2x r2y (pt_l2ge_TR E F (G:ℝ) hE hEF hGr hba) (pt_l2ge_TRR E F (G:ℝ) hE hEF hGr hba) (pt_l2ge_BL E F (G:ℝ) hE hEF hGr hba) (pt_l2ge_E E F (G:ℝ) hE hEF hGr hba)
  have inL : ∀ p ∈ Preg (pO E F) (pP1 E F) (pC0 E F) (((0 : ℕ) : ℝ) / (kc : ℝ)), InT E F ((G:ℝ)+1) p :=
    preg_inT E F _ _ _ _ (pO E F) (pO E F) _ hσ0L hσ1L (eL _ rfl).1 (eL _ rfl).2 (eL2 _ rfl).1 (eL2 _ rfl).2
      (inT_O E F (G:ℝ) hE hEF hGr hba) (inT_O E F (G:ℝ) hE hEF hGr hba) (inT_P1 E F (G:ℝ) hE hEF hGr hba) (inT_C0 E F (G:ℝ) hE hEF hGr hba)
  have inM : ∀ p ∈ Preg (pQ E F) (pTR E F) (pP1 E F) ((spM : ℝ) / (kb : ℝ)), InT E F ((G:ℝ)+1) p :=
    preg_inT E F _ _ _ _ (pBL E F) (pC0 E F) _ hσ0M hσ1M m1x m1y m2x m2y
      (inT_BL E F (G:ℝ) hE hEF hGr hba) (inT_C0 E F (G:ℝ) hE hEF hGr hba) (inT_TR E F (G:ℝ) hE hEF hGr hba) (inT_P1 E F (G:ℝ) hE hEF hGr hba)
  have inR : ∀ p ∈ Preg (pR E F (apn : ℝ)) (pBL E F) (pE E F ((G:ℝ)+1)) ((apn : ℝ) / ((kb + apn : ℕ) : ℝ)), InT E F ((G:ℝ)+1) p :=
    preg_inT E F _ _ _ _ (pTR E F) (pTRR E F ((G:ℝ)+1)) _ hσ0R hσ1R r1x r1y r2x r2y
      (inT_TR E F (G:ℝ) hE hEF hGr hba) (inT_TRR E F (G:ℝ) hE hEF hGr hba) (inT_BL E F (G:ℝ) hE hEF hGr hba) (inT_E E F (G:ℝ) hE hEF hGr hba)
  have macInT := mac_inT E F (G:ℝ) hE hEF hGr hba
  have hab : E * F * (F ^ 2 - E ^ 2) ≠ 0 := (mul_pos ha hb).ne'
  have hu : E * F ≠ 0 := ha.ne'
  have d01 : Disjoint (interior (Phi φ '' Preg (pO E F) (pP1 E F) (pC0 E F) (((0 : ℕ) : ℝ) / (kc : ℝ))))
      (interior (Phi φ '' Preg (pQ E F) (pTR E F) (pP1 E F) ((spM : ℝ) / (kb : ℝ)))) :=
    disjoint_image hφ (interior_disj_lin _ _ _ hab l1le_L l1ge_M)
  have d02 : Disjoint (interior (Phi φ '' Preg (pO E F) (pP1 E F) (pC0 E F) (((0 : ℕ) : ℝ) / (kc : ℝ))))
      (interior (Phi φ '' Preg (pR E F (apn : ℝ)) (pBL E F) (pE E F ((G:ℝ)+1)) ((apn : ℝ) / ((kb + apn : ℕ) : ℝ)))) :=
    disjoint_image hφ (interior_disj_lin _ _ _ hab l1le_L l1ge_R)
  have d12 : Disjoint (interior (Phi φ '' Preg (pQ E F) (pTR E F) (pP1 E F) ((spM : ℝ) / (kb : ℝ))))
      (interior (Phi φ '' Preg (pR E F (apn : ℝ)) (pBL E F) (pE E F ((G:ℝ)+1)) ((apn : ℝ) / ((kb + apn : ℕ) : ℝ)))) :=
    disjoint_image hφ (interior_disj_lin _ _ _ hu l2le_M l2ge_R)
  have d03 : Disjoint (interior (Phi φ '' Preg (pO E F) (pP1 E F) (pC0 E F) (((0 : ℕ) : ℝ) / (kc : ℝ))))
      (interior (Phi φ '' Sh (pP1 E F) H)) :=
    disjoint_image hφ (interior_disj_snd (E*F*(F^2-E^2)) (fun p hp => by have := Yle_L p hp; linarith)
      (fun p hp => (macInT p hp).2))
  have d13 : Disjoint (interior (Phi φ '' Preg (pQ E F) (pTR E F) (pP1 E F) ((spM : ℝ) / (kb : ℝ))))
      (interior (Phi φ '' Sh (pP1 E F) H)) :=
    disjoint_image hφ (interior_disj_snd (E*F*(F^2-E^2)) (fun p hp => by have := Yle_M p hp; linarith)
      (fun p hp => (macInT p hp).2))
  have d23 : Disjoint (interior (Phi φ '' Preg (pR E F (apn : ℝ)) (pBL E F) (pE E F ((G:ℝ)+1)) ((apn : ℝ) / ((kb + apn : ℕ) : ℝ))))
      (interior (Phi φ '' Sh (pP1 E F) H)) :=
    disjoint_image hφ (interior_disj_snd (E*F*(F^2-E^2)) (fun p hp => by have := Yle_R p hp; linarith)
      (fun p hp => (macInT p hp).2))
  have hg0 : (0 : ℝ) < (G : ℝ) + 1 := by linarith
  have hB0 : 0 < pB0 E F := by unfold pB0; positivity
  have hdetT : ((pB0 E F * ((G : ℝ) + 1), (0 : ℝ)).1 - ((0 : ℝ), (0 : ℝ)).1) *
      (((F^2-E^2)^2 * ((G : ℝ) + 1), E*F*(F^2-E^2) * ((G : ℝ) + 1)).2 - ((0 : ℝ), (0 : ℝ)).2) -
      (((F^2-E^2)^2 * ((G : ℝ) + 1), E*F*(F^2-E^2) * ((G : ℝ) + 1)).1 - ((0 : ℝ), (0 : ℝ)).1) *
      ((pB0 E F * ((G : ℝ) + 1), (0 : ℝ)).2 - ((0 : ℝ), (0 : ℝ)).2) ≠ 0 := by
    have : ((pB0 E F * ((G : ℝ) + 1), (0 : ℝ)).1 - ((0 : ℝ), (0 : ℝ)).1) *
      (((F^2-E^2)^2 * ((G : ℝ) + 1), E*F*(F^2-E^2) * ((G : ℝ) + 1)).2 - ((0 : ℝ), (0 : ℝ)).2) -
      (((F^2-E^2)^2 * ((G : ℝ) + 1), E*F*(F^2-E^2) * ((G : ℝ) + 1)).1 - ((0 : ℝ), (0 : ℝ)).1) *
      ((pB0 E F * ((G : ℝ) + 1), (0 : ℝ)).2 - ((0 : ℝ), (0 : ℝ)).2) = pB0 E F * ((G : ℝ) + 1) * (E*F*(F^2-E^2) * ((G : ℝ) + 1)) := by
      simp only []; ring
    rw [this]
    exact (mul_pos (mul_pos hB0 hg0) (mul_pos (mul_pos ha hb) hg0)).ne'
  let tgt : Tri := triC φ hφ ((0 : ℝ), (0 : ℝ)) (pB0 E F * ((G : ℝ) + 1), 0)
    ((F^2-E^2)^2 * ((G : ℝ) + 1), E*F*(F^2-E^2) * ((G : ℝ) + 1)) hdetT
  have tgt_car : tgt.carrier = TG φ E F ((G : ℝ) + 1) := carrier_triC _ _ _ _ _ _
  let S : Fin 4 → Set Plane := ![Phi φ '' Preg (pO E F) (pP1 E F) (pC0 E F) (((0 : ℕ) : ℝ) / (kc : ℝ)),
    Phi φ '' Preg (pQ E F) (pTR E F) (pP1 E F) ((spM : ℝ) / (kb : ℝ)),
    Phi φ '' Preg (pR E F (apn : ℝ)) (pBL E F) (pE E F ((G:ℝ)+1)) ((apn : ℝ) / ((kb + apn : ℕ) : ℝ)),
    Phi φ '' Sh (pP1 E F) H]
  let n : Fin 4 → ℕ := ![kc * kc - 0 * 0, kb * kb - spM * spM, (kb + apn) * (kb + apn) - apn * apn, N0 * G * G]
  let Rf : ∀ a : Fin 4, TFam (S a) M (n a) := fun a => match a with
    | ⟨0, _⟩ => famL
    | ⟨1, _⟩ => famM
    | ⟨2, _⟩ => famR
    | ⟨3, _⟩ => famMac
    | ⟨k + 4, h⟩ => absurd h (by omega)
  have hSd : ∀ a b : Fin 4, a ≠ b → Disjoint (interior (S a)) (interior (S b)) := by
    intro a b hab
    fin_cases a <;> fin_cases b <;>
      first
        | exact absurd rfl hab
        | exact d01 | exact d01.symm | exact d02 | exact d02.symm | exact d03 | exact d03.symm
        | exact d12 | exact d12.symm | exact d13 | exact d13.symm | exact d23 | exact d23.symm
  have hsub : ∀ a : Fin 4, S a ⊆ tgt.carrier := by
    intro a
    rw [tgt_car]
    fin_cases a
    · exact Set.image_mono (fun p hp => inT_mem E F _ hE hEF hg0 hba (inL p hp))
    · exact Set.image_mono (fun p hp => inT_mem E F _ hE hEF hg0 hba (inM p hp))
    · exact Set.image_mono (fun p hp => inT_mem E F _ hE hEF hg0 hba (inR p hp))
    · exact Set.image_mono (fun p hp => inT_mem E F _ hE hEF hg0 hba (macInT p hp).1)
  have hsum : (∑ a, n a) = N0 * (G + 1) * (G + 1) := by
    have h2 : spM * spM ≤ kb * kb := Nat.mul_self_le_mul_self hspk
    have h3 : apn * apn ≤ (kb + apn) * (kb + apn) := Nat.mul_self_le_mul_self hapk
    have e : (∑ a, n a) = kc * kc + (kb * kb - spM * spM) + ((kb + apn) * (kb + apn) - apn * apn) + N0 * G * G := by
      rw [Fin.sum_univ_four]
      show kc * kc - 0 * 0 + (kb * kb - spM * spM) + ((kb + apn) * (kb + apn) - apn * apn) + N0 * G * G = _
      simp
    rw [e]
    apply Nat.cast_injective (R := ℝ)
    push_cast [Nat.cast_sub h2, Nat.cast_sub h3]
    rw [hkc, hkb, hsp, hap, hN0]
    ring
  have hvol : ((∑ a, n a : ℕ) : ENNReal) * volume M.carrier = volume tgt.carrier := by
    have hs := sD_pos hφ
    have hφ0 : 0 < φ := by linarith
    have hM : volume M.carrier = ENNReal.ofReal (sD φ / (2 * φ) * ((F ^ 2 - E ^ 2) * (E * F)))
        * volume Erdos634.AreaDet.stdCarrier := by
      rw [hMdef]; unfold brickL; rw [vol_triC]; congr 2
      rw [← abs_of_pos (show 0 < sD φ / (2 * φ) * ((F ^ 2 - E ^ 2) * (E * F)) from
        mul_pos (div_pos hs (by linarith)) (mul_pos hb ha))]
      congr 1; simp only []; ring
    have hT : volume tgt.carrier = ENNReal.ofReal (sD φ / (2 * φ) * (pB0 E F * ((G : ℝ) + 1) * (E*F*(F^2-E^2) * ((G : ℝ) + 1))))
        * volume Erdos634.AreaDet.stdCarrier := by
      change volume (triC φ hφ _ _ _ hdetT).carrier = _
      rw [vol_triC]; congr 2
      rw [← abs_of_pos (show 0 < sD φ / (2 * φ) * (pB0 E F * ((G : ℝ) + 1) * (E*F*(F^2-E^2) * ((G : ℝ) + 1))) from
        mul_pos (div_pos hs (by linarith)) (mul_pos (mul_pos hB0 hg0) (mul_pos (mul_pos ha hb) hg0)))]
      congr 1; simp only []; ring
    rw [hM, hT, hsum, ← mul_assoc, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    congr 2
    push_cast
    rw [hN0]; unfold pB0; ring
  obtain ⟨D, hDm, hDt⟩ := pack_exists' (M := M) (T := tgt) S n Rf hSd hsub hvol
  have key : ∀ N : ℕ, N = N0 * (G + 1) * (G + 1) → ∀ D : CongruentDissection N, D.model = M → D.target = tgt →
      Nonempty (RTiling (TG φ E F ((G : ℝ) + 1)) M (N0 * (G + 1) * (G + 1)) ) := by
    rintro N rfl D hm ht
    exact ⟨{ tile := D.tile
             covers := D.covers.trans (by rw [ht, tgt_car])
             disj := D.interiors_disjoint
             cong := fun i => by have := D.tiles_congruent i; rwa [hm] at this }⟩
  exact key _ hsum D hDm hDt

end
end Erdos634.Draft.CollarLayer
