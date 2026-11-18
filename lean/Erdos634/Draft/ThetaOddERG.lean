-- Draft/ThetaOddERG.lean -- ODD-E formalization, module 11: the R group of Theorem B (P1 red rows + left column + z/e right columns).
-- INTERNAL BUILD ONLY, UNAUDITED beyond internal checks.  No sorry, no native_decide.
/-
`rgHP`: the pentagon `Rh` minus the corner `(en) tau` is tiled by `2 r (w/e) b + [2 f n m + (en)^2 + 2 e n x] + (w f/e - n) [2 e^2 + 2 f m + 2 e (e n + x - e)]` tiles:
P1 red rows `[0,p] x [V1,H]`, the left column `[0,en]` (G, T1, B = P2, P3, P4), and `cn = w f / e - n` right columns of width `e` (T0, G, T1, B = P5-P8)
(the AI assistant's Theorem B, RESULT.md S2 B.2-B.3).  Credit: the AI assistant's Theorem B; Beeson-Rosu (cells); the project.  INTERNAL BUILD ONLY, UNAUDITED beyond internal checks.
-/
import Erdos634.Draft.ThetaOddEColJ

open scoped Classical
open Erdos634.Geometry Erdos634.CertCoord

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Erdos634.Draft.ThetaNotch
noncomputable section
open Erdos634.Draft.WFrameF Erdos634.Draft.RegionTiling Erdos634.Draft.WBrickF Erdos634.Draft.CollarLayer
open Erdos634.Draft.LadderFam Erdos634.Draft.CollarFam

section rg
variable {φ : ℝ} (hφ : 1 < φ) (e f : ℕ) (he : 0 < e) (hef : e < f) (hφE : φ = (f : ℝ) / e)

/-- the corner triangle `T0` of a right column -/
def t0Piece (s M K : ℝ) (u0 : ℝ) (lam : ℕ) (hl : 0 < lam) :
    HPs φ (Mrow hφ e f he hef) (e : ℝ) f s M K ⟨u0, u0 + ((e * lam : ℕ) : ℝ), 0, ((e * lam : ℕ) : ℝ), u0, u0 + ((e * lam : ℕ) : ℝ)⟩
      ((e * lam) * (e * lam)) := by
  set L : ℝ := ((e * lam : ℕ) : ℝ) with hLdef
  have hL : 0 < L := by rw [hLdef]; exact_mod_cast Nat.mul_pos he hl
  refine triPiece hφ e f he hef hφE s M K u0 0 (u0 + L) 0 u0 L (e * lam) (Nat.mul_pos he hl)
    ⟨u0, u0 + L, 0, L, u0, u0 + L⟩ (by nlinarith)
    (((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ^ 2) (((f : ℝ) ^ 2) ^ 2) (((e : ℝ) * f) ^ 2)
    (by unfold Qc; rw [hLdef]; ring) (by unfold Qc; rw [hLdef]; ring) (by unfold Qc; rw [hLdef]; ring)
    (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)) ?_
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩ <;> linarith

set_option maxHeartbeats 4000000 in
/-- the red rows `P1` -/
def p1Piece (b wq r : ℕ) (hb : (b : ℝ) = (f : ℝ) ^ 2 - (e : ℝ) ^ 2) (s M K p V1 H ab ba : ℝ)
    (hab : ab = (e : ℝ) * f / ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)) (hba : ba = ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) / ((e : ℝ) * f))
    (hP1 : ((wq * b : ℕ) : ℝ) * ab = p) (hQ : (r : ℝ) * ba = H - V1) (hp0 : 0 ≤ p) (hHV : V1 ≤ H) (hV0 : 0 ≤ V1) :
    HPs φ (Mrow hφ e f he hef) (e : ℝ) f s M K ⟨0, p, V1, H, V1, p + H⟩ (2 * (wq * b) * r) := by
  have hE : (0 : ℝ) < e := by exact_mod_cast he
  have hEF : (e : ℝ) < f := by exact_mod_cast hef
  have hF : (0 : ℝ) < f := by linarith
  have hb0 : (0 : ℝ) < (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by nlinarith
  have habne : ab ≠ 0 := by rw [hab]; positivity
  have hab_ba : ab * ba = 1 := by rw [hab, hba]; field_simp
  refine parPiece hφ e f he hef hφE s M K 0 V1 ab 0 0 ba (wq * b) r ⟨0, p, V1, H, V1, p + H⟩
    (by intro h; nlinarith [hab_ba])
    (((e : ℝ) * f) ^ 2) (((f : ℝ) ^ 2) ^ 2) (((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ^ 2)
    (by unfold Qc; rw [hab]; field_simp; ring)
    (by unfold Qc; rw [hab, hba]; field_simp; ring)
    (by unfold Qc; rw [hba]; field_simp; ring)
    (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)))) ?_
  intro hp hq
  refine ⟨?_, ?_, ?_, ?_⟩ <;> refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

end rg

end

end Erdos634.Draft.ThetaNotch
