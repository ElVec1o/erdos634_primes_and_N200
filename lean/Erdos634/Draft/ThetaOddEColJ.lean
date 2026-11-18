-- Draft/ThetaOddEColJ.lean -- ODD-E formalization, module 10: a column of Theorem B = T0 + G + T1 + B joined.
-- INTERNAL BUILD ONLY, UNAUDITED beyond internal checks.  No sorry, no native_decide.
/-
See `ThetaOddECol`.  Credit: the AI assistant's Theorem B; Beeson-Rosu (cells); the project.  INTERNAL BUILD ONLY, UNAUDITED beyond internal checks.
-/
import Erdos634.Draft.ThetaOddECol

open scoped Classical
open Erdos634.Geometry Erdos634.CertCoord

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Erdos634.Draft.ThetaNotch
noncomputable section
open Erdos634.Draft.WFrameF Erdos634.Draft.RegionTiling Erdos634.Draft.WBrickF Erdos634.Draft.CollarLayer
open Erdos634.Draft.LadderFam Erdos634.Draft.CollarFam

section col
variable {φ : ℝ} (hφ : 1 < φ) (e f : ℕ) (he : 0 < e) (hef : e < f) (hφE : φ = (f : ℝ) / e)

set_option maxHeartbeats 8000000 in
/-- a column: optional corner triangle `T0` (any piece with a box `bT` inside the column and separated from `G, T1, B`) + `G + T1 + B` -/
def colHP (s M K mu : ℝ) (m : ℕ) (hmu : mu = (m : ℝ) * f / e) (ac ca : ℝ) (hac : ac = (e : ℝ) * f / (f : ℝ) ^ 2)
    (hca : ca = (f : ℝ) ^ 2 / ((e : ℝ) * f)) (u0 : ℝ) (lam : ℕ) (hl : 0 < lam) (R : ℕ) (V1 : ℝ)
    (hV1 : V1 = ((e * lam : ℕ) : ℝ) + mu + R) (cslo : ℝ) (hcs : cslo ≤ u0 + ((e * lam : ℕ) : ℝ))
    (bT : OBx) (n0 : ℕ) (T0 : HPs φ (Mrow hφ e f he hef) (e : ℝ) f s M K bT n0)
    (hT1 : u0 ≤ bT.ulo ∧ bT.uhi ≤ u0 + ((e * lam : ℕ) : ℝ) ∧ 0 ≤ bT.vlo ∧ bT.vhi ≤ V1 ∧ cslo ≤ bT.slo ∧
      bT.shi ≤ u0 + ((e * lam : ℕ) : ℝ) + V1)
    (hT2 : OSep bT ⟨u0, u0 + ((e * lam : ℕ) : ℝ), 0, ((e * lam : ℕ) : ℝ) + mu, u0 + ((e * lam : ℕ) : ℝ), u0 + ((e * lam : ℕ) : ℝ) + mu⟩)
    (hT3 : OSep bT ⟨u0, u0 + ((e * lam : ℕ) : ℝ), mu, ((e * lam : ℕ) : ℝ) + mu, u0 + ((e * lam : ℕ) : ℝ) + mu,
      u0 + 2 * ((e * lam : ℕ) : ℝ) + mu⟩)
    (hT4 : OSep bT ⟨u0, u0 + ((e * lam : ℕ) : ℝ), ((e * lam : ℕ) : ℝ) + mu, V1, u0 + ((e * lam : ℕ) : ℝ) + mu,
      u0 + ((e * lam : ℕ) : ℝ) + V1⟩) :
    HPs φ (Mrow hφ e f he hef) (e : ℝ) f s M K ⟨u0, u0 + ((e * lam : ℕ) : ℝ), 0, V1, cslo, u0 + ((e * lam : ℕ) : ℝ) + V1⟩
      (n0 + 2 * (f * lam) * m + (e * lam) * (e * lam) + 2 * (e * lam) * R) := by
  have hE : (0 : ℝ) < e := by exact_mod_cast he
  have hEF : (e : ℝ) < f := by exact_mod_cast hef
  set L : ℝ := ((e * lam : ℕ) : ℝ) with hLdef
  have hL : 0 < L := by rw [hLdef]; exact_mod_cast Nat.mul_pos he hl
  have hmu0 : 0 ≤ mu := by rw [hmu]; positivity
  have hR0 : (0 : ℝ) ≤ R := Nat.cast_nonneg R
  have G := gPiece hφ e f he hef hφE s M K mu m hmu ac ca hac hca u0 lam hl
  have T1 := t1Piece hφ e f he hef hφE s M K mu hmu0 u0 lam hl
  have B := bPiece hφ e f he hef hφE s M K mu hmu0 u0 lam hl R V1 hV1
  refine castHPs (hexJoinF hE hEF hφ
    ![bT, ⟨u0, u0 + L, 0, L + mu, u0 + L, u0 + L + mu⟩, ⟨u0, u0 + L, mu, L + mu, u0 + L + mu, u0 + 2 * L + mu⟩,
      ⟨u0, u0 + L, L + mu, V1, u0 + L + mu, u0 + L + V1⟩]
    ![n0, 2 * (f * lam) * m, (e * lam) * (e * lam), 2 * (e * lam) * R]
    (fun a => match a with | ⟨0, _⟩ => T0 | ⟨1, _⟩ => G | ⟨2, _⟩ => T1 | ⟨3, _⟩ => B | ⟨k + 4, h⟩ => absurd h (by omega))
    ⟨u0, u0 + L, 0, V1, cslo, u0 + L + V1⟩ ?_ ?_) ?_
  · intro a
    obtain ⟨t1, t2, t3, t4, t5, t6⟩ := hT1
    fin_cases a <;> refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (try simp) <;> linarith
  · intro a b hab
    fin_cases a <;> fin_cases b <;> first | exact absurd rfl hab | skip
    all_goals simp [OSep]
    all_goals first | (left; linarith) | (right; left; linarith) | (right; right; left; linarith) | (right; right; right; left; linarith) | (right; right; right; right; left; linarith) | (right; right; right; right; right; linarith) | (simp only [OSep] at hT2 hT3 hT4; tauto)
  · simp [Fin.sum_univ_four] <;> ring

end col

end

end Erdos634.Draft.ThetaNotch
