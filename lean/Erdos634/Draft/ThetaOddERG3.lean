-- Draft/ThetaOddERG3.lean -- ODD-E formalization, module 13: the full R group `rgHP` = P1 + left column + right block, and its tile family on `rReg2`.
-- INTERNAL BUILD ONLY, UNAUDITED beyond internal checks.  No sorry, no native_decide.
/-
Credit: the AI assistant's Theorem B; Beeson-Rosu (cells); the project.  INTERNAL BUILD ONLY, UNAUDITED beyond internal checks.
-/
import Erdos634.Draft.ThetaOddERG2

open scoped Classical
open Erdos634.Geometry Erdos634.CertCoord

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Erdos634.Draft.ThetaNotch
noncomputable section
open Erdos634.Draft.WFrameF Erdos634.Draft.RegionTiling Erdos634.Draft.WBrickF Erdos634.Draft.CollarLayer
open Erdos634.Draft.LadderFam Erdos634.Draft.CollarFam

section rg3
variable {φ : ℝ} (hφ : 1 < φ) (e f : ℕ) (he : 0 < e) (hef : e < f) (hφE : φ = (f : ℝ) / e)

set_option maxHeartbeats 16000000 in
/-- **the R group**: `Rh` minus the corner, tiled; count `2 r wq b + (2 f n m + (en)^2 + 2 e n x) + cn (2 e^2 + 2 f m + 2 e (e n + x - e))` -/
def rgHP (s M K : ℝ) (b wq r n x m cn : ℕ) (hb : (b : ℝ) = (f : ℝ) ^ 2 - (e : ℝ) ^ 2) (hn : 1 ≤ n) (hcn : cn + n = wq * f)
    (mu V1 H p ac ca ab ba : ℝ) (hmu : mu = (m : ℝ) * f / e) (hac : ac = (e : ℝ) * f / (f : ℝ) ^ 2)
    (hca : ca = (f : ℝ) ^ 2 / ((e : ℝ) * f)) (hab : ab = (e : ℝ) * f / ((f : ℝ) ^ 2 - (e : ℝ) ^ 2))
    (hba : ba = ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) / ((e : ℝ) * f)) (hV1 : V1 = (e : ℝ) * n + x + mu) (hH : H = V1 + (r : ℝ) * ba)
    (hp : p = (e : ℝ) * n + (cn : ℝ) * e) :
    HPs φ (Mrow hφ e f he hef) (e : ℝ) f s M K ⟨0, p, 0, H, ((e * n : ℕ) : ℝ), p + H⟩
      (2 * (wq * b) * r + (0 + 2 * (f * n) * m + (e * n) * (e * n) + 2 * (e * n) * x) +
        cn * ((e * 1) * (e * 1) + 2 * (f * 1) * m + (e * 1) * (e * 1) + 2 * (e * 1) * (e * n + x - e * 1))) := by
  have hE : (0 : ℝ) < e := by exact_mod_cast he
  have hEF : (e : ℝ) < f := by exact_mod_cast hef
  have hF : (0 : ℝ) < f := by linarith
  have hb0 : (0 : ℝ) < (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by nlinarith
  have hmu0 : 0 ≤ mu := by rw [hmu]; positivity
  have hEnC : ((e * n : ℕ) : ℝ) = (e : ℝ) * n := by push_cast; ring
  set En : ℝ := ((e * n : ℕ) : ℝ) with hEn
  have hEn0 : 0 ≤ En := by rw [hEnC]; positivity
  have hn' : 0 < n := hn
  have hcnR : (cn : ℝ) + n = wq * f := by exact_mod_cast hcn
  have hba0 : 0 < ba := by rw [hba]; positivity
  have hrba : 0 ≤ (r : ℝ) * ba := by positivity
  have hxR : (0 : ℝ) ≤ x := Nat.cast_nonneg _
  have hcnR0 : (0 : ℝ) ≤ cn := Nat.cast_nonneg _
  have hV1' : V1 = En + mu + (x : ℝ) := by rw [hV1, hEnC]; ring
  have hp' : p = En + (cn : ℝ) * e := by rw [hp, hEnC]
  have hpw : p = (wq : ℝ) * e * f := by rw [hp]; linear_combination (e : ℝ) * hcnR
  have hP1 : ((wq * b : ℕ) : ℝ) * ab = p := by
    rw [hpw, hab]; push_cast; rw [hb]; field_simp
  have hp0 : 0 ≤ p := by rw [hp']; positivity
  have hHV : V1 ≤ H := by rw [hH]; linarith
  have hV0 : 0 ≤ V1 := by rw [hV1']; linarith
  have P1 := p1Piece hφ e f he hef hφE b wq r hb s M K p V1 H ab ba hab hba hP1 (by rw [hH]; ring) hp0 hHV hV0
  -- left column
  have hL0 : (0 : ℝ) ≤ En := hEn0
  have Left := colHP hφ e f he hef hφE s M K mu m hmu ac ca hac hca 0 n hn' x V1 (by rw [hV1']) En (by rw [zero_add])
    ⟨0, 0, 0, 0, En, En⟩ 0 (emptyHP _) ?_ ?_ ?_ ?_
  · -- right block
    have Right := rightBlock hφ e f he hef hφE s M K mu m hmu ac ca hac hca n x cn hn V1
      (by have hsub : e ≤ e * n + x := by nlinarith
          simp only [mul_one]; push_cast [Nat.cast_sub hsub]; rw [hV1]; ring) En hEn
    have J := hexJoinF hE hEF hφ
      ![(⟨0, p, V1, H, V1, p + H⟩ : OBx), ⟨0, 0 + En, 0, V1, En, 0 + En + V1⟩, ⟨En, En + (cn : ℝ) * e, 0, V1, En, En + (cn : ℝ) * e + V1⟩]
      ![2 * (wq * b) * r, 0 + 2 * (f * n) * m + (e * n) * (e * n) + 2 * (e * n) * x,
        cn * ((e * 1) * (e * 1) + 2 * (f * 1) * m + (e * 1) * (e * 1) + 2 * (e * 1) * (e * n + x - e * 1))]
      (fun a => match a with | ⟨0, _⟩ => P1 | ⟨1, _⟩ => Left | ⟨2, _⟩ => Right | ⟨k + 3, h⟩ => absurd h (by omega))
      ⟨0, p, 0, H, En, p + H⟩ ?_ ?_
    · refine castHPs J ?_
      simp [Fin.sum_univ_three]
    · intro a
      fin_cases a <;> refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (try simp) <;> nlinarith
    · intro a b hab
      fin_cases a <;> fin_cases b <;> first | exact absurd rfl hab | skip
      all_goals simp [OSep]
      all_goals first | (left; linarith) | (right; left; linarith) | (right; right; left; linarith) | (right; right; right; left; linarith) | (right; right; right; right; left; linarith) | (right; right; right; right; right; linarith)
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp <;> linarith
  · refine Or.inr (Or.inr (Or.inl ?_)); simp
  · refine Or.inr (Or.inr (Or.inl ?_)); simp; linarith
  · refine Or.inr (Or.inr (Or.inl ?_)); simp; linarith

end rg3

end

end Erdos634.Draft.ThetaNotch
