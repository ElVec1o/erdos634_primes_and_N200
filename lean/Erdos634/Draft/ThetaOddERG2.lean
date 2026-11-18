-- Draft/ThetaOddERG2.lean -- ODD-E formalization, module 12: assembly of the R group of Theorem B (P1 + left column + right columns).
-- INTERNAL BUILD ONLY, UNAUDITED beyond internal checks.  No sorry, no native_decide.
/-
See `ThetaOddERG`.  Credit: the AI assistant's Theorem B; Beeson-Rosu (cells); the project.  INTERNAL BUILD ONLY, UNAUDITED beyond internal checks.
-/
import Erdos634.Draft.ThetaOddERG

open scoped Classical
open Erdos634.Geometry Erdos634.CertCoord

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Erdos634.Draft.ThetaNotch
noncomputable section
open Erdos634.Draft.WFrameF Erdos634.Draft.RegionTiling Erdos634.Draft.WBrickF Erdos634.Draft.CollarLayer
open Erdos634.Draft.LadderFam Erdos634.Draft.CollarFam

section rg2
variable {φ : ℝ} (hφ : 1 < φ) (e f : ℕ) (he : 0 < e) (hef : e < f) (hφE : φ = (f : ℝ) / e)

set_option maxHeartbeats 16000000 in
/-- the right block: `cn` columns of width `e` starting at `u = en` -/
def rightBlock (s M K mu : ℝ) (m : ℕ) (hmu : mu = (m : ℝ) * f / e) (ac ca : ℝ) (hac : ac = (e : ℝ) * f / (f : ℝ) ^ 2)
    (hca : ca = (f : ℝ) ^ 2 / ((e : ℝ) * f)) (n x cn : ℕ) (hn : 1 ≤ n) (V1 : ℝ)
    (hV1 : V1 = ((e * 1 : ℕ) : ℝ) + mu + ((e * n + x - e * 1 : ℕ) : ℝ)) (En : ℝ) (hEn : En = ((e * n : ℕ) : ℝ)) :
    HPs φ (Mrow hφ e f he hef) (e : ℝ) f s M K ⟨En, En + (cn : ℝ) * e, 0, V1, En, En + (cn : ℝ) * e + V1⟩
      (cn * ((e * 1) * (e * 1) + 2 * (f * 1) * m + (e * 1) * (e * 1) + 2 * (e * 1) * (e * n + x - e * 1))) := by
  have hE : (0 : ℝ) < e := by exact_mod_cast he
  have hEF : (e : ℝ) < f := by exact_mod_cast hef
  have hmu0 : 0 ≤ mu := by rw [hmu]; positivity
  have hEn0 : 0 ≤ En := by rw [hEn]; positivity
  have hL1 : ((e * 1 : ℕ) : ℝ) = (e : ℝ) := by simp
  have hR0 : (0 : ℝ) ≤ ((e * n + x - e * 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hV0 : (e : ℝ) ≤ V1 := by rw [hV1, hL1]; linarith
  have hcol : ∀ i : Fin cn, HPs φ (Mrow hφ e f he hef) (e : ℝ) f s M K
      ⟨En + (i : ℝ) * e, En + (i : ℝ) * e + ((e * 1 : ℕ) : ℝ), 0, V1, En + (i : ℝ) * e,
        En + (i : ℝ) * e + ((e * 1 : ℕ) : ℝ) + V1⟩
      ((e * 1) * (e * 1) + 2 * (f * 1) * m + (e * 1) * (e * 1) + 2 * (e * 1) * (e * n + x - e * 1)) := by
    intro i
    have hi0 : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg _
    refine colHP hφ e f he hef hφE s M K mu m hmu ac ca hac hca (En + (i : ℝ) * e) 1 Nat.one_pos (e * n + x - e * 1) V1 hV1
      (En + (i : ℝ) * e) (by rw [hL1]; linarith)
      ⟨En + (i : ℝ) * e, En + (i : ℝ) * e + ((e * 1 : ℕ) : ℝ), 0, ((e * 1 : ℕ) : ℝ), En + (i : ℝ) * e,
        En + (i : ℝ) * e + ((e * 1 : ℕ) : ℝ)⟩ ((e * 1) * (e * 1))
      (t0Piece hφ e f he hef hφE s M K (En + (i : ℝ) * e) 1 Nat.one_pos) ?_ ?_ ?_ ?_
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [hL1] <;> nlinarith
    · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))); simp only [hL1]; linarith
    · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))); simp only [hL1]; linarith
    · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))); simp only [hL1]; linarith
  have J := hexJoinF hE hEF hφ (fun i : Fin cn => (⟨En + (i : ℝ) * e, En + (i : ℝ) * e + ((e * 1 : ℕ) : ℝ), 0, V1, En + (i : ℝ) * e,
        En + (i : ℝ) * e + ((e * 1 : ℕ) : ℝ) + V1⟩ : OBx))
    (fun _ => (e * 1) * (e * 1) + 2 * (f * 1) * m + (e * 1) * (e * 1) + 2 * (e * 1) * (e * n + x - e * 1)) hcol
    ⟨En, En + (cn : ℝ) * e, 0, V1, En, En + (cn : ℝ) * e + V1⟩ ?_ ?_
  · refine castHPs J ?_
    simp
  · intro i
    have hi : (i : ℝ) + 1 ≤ cn := by exact_mod_cast i.2
    have hi0 : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg _
    simp only [hL1]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> nlinarith
  · intro i j hij
    have hne : (i : ℕ) ≠ (j : ℕ) := fun h => hij (Fin.ext h)
    rcases lt_or_gt_of_ne hne with h | h
    · have : (i : ℝ) + 1 ≤ j := by exact_mod_cast h
      refine Or.inl ?_; simp only [hL1]; nlinarith
    · have : (j : ℝ) + 1 ≤ i := by exact_mod_cast h
      refine Or.inr (Or.inl ?_); simp only [hL1]; nlinarith

end rg2

end

end Erdos634.Draft.ThetaNotch
