-- Draft/ThetaNotchL2.lean -- the L group family: the `k = j f` strips `n = s-k, ..., s-1` tile `{y <= k, x+y <= s}`.
-- INTERNAL BUILD ONLY, UNAUDITED.  No sorry, no native_decide.
/-
Credit: Paliy (annulus/band steps on a seed), Beeson-Rosu (frame), project (`ThetaUnitStep`).  INTERNAL BUILD ONLY, UNAUDITED.
-/
import Erdos634.Draft.ThetaNotchL

open scoped Classical
open Erdos634.Geometry Erdos634.CertCoord

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Erdos634.Draft.ThetaNotch
noncomputable section
open Erdos634.Draft.WFrameF Erdos634.Draft.RegionTiling Erdos634.Draft.WBrickF Erdos634.Draft.CollarLayer
open Erdos634.Draft.LadderFam Erdos634.Draft.CollarFam
open Erdos634.Draft.ThetaUnit (gg)

theorem bands_disj {E F : ℝ} (hE : 0 < E) (hEF : E < F) (n n' : ℝ) (h : n + 1 ≤ n') :
    Disjoint (interior (bandReg E F n)) (interior (bandReg E F n')) := by
  obtain ⟨hF, hb⟩ := frame_pos hE hEF
  have hEFB : 0 < E * F * (F ^ 2 - E ^ 2) := by positivity
  refine interior_disj_lin (A := bandReg E F n) (B := bandReg E F n') E F (E * F * (F ^ 2 - E ^ 2) * (n + 1)) hE.ne' ?_ ?_
  · rintro p ⟨-, -, -, h4⟩; exact h4
  · rintro p ⟨-, -, h3, -⟩
    have : E * F * (F ^ 2 - E ^ 2) * (n + 1) ≤ E * F * (F ^ 2 - E ^ 2) * n' := mul_le_mul_of_nonneg_left h hEFB.le
    linarith

namespace NP
variable (P : NP)

def n0 : ℕ := P.s - P.j * P.f
def kk : ℕ := P.j * P.f

theorem n0_add : P.n0 + P.kk = P.s := by
  unfold n0 kk; have := P.hks; omega

theorem hgn0 : P.e ≤ (P.f - P.e) * P.n0 := by
  have hD := P.hD
  have h1 : P.f - P.e = P.g := by have := P.hfg; omega
  rw [h1]
  have h2 := P.n0_add
  unfold kk at h2
  have : P.g * P.s = P.g * P.n0 + P.g * (P.j * P.f) := by rw [← Nat.mul_add, ← h2]
  omega

theorem strip_hg (i : ℕ) : P.e ≤ (P.f - P.e) * (P.n0 + i) := by
  have := P.hgn0
  calc P.e ≤ (P.f - P.e) * P.n0 := this
    _ ≤ (P.f - P.e) * (P.n0 + i) := Nat.mul_le_mul_left _ (Nat.le_add_right _ _)

theorem sum_strips (k : ℕ) (n0 : ℕ) : (∑ i : Fin k, P.b * (2 * (n0 + (i : ℕ)) + 1)) = P.b * ((n0 + k) * (n0 + k) - n0 * n0) := by
  rw [Fin.sum_univ_eq_sum_range (fun i => P.b * (2 * (n0 + i) + 1)) k]
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    have h1 : n0 * n0 ≤ (n0 + k) * (n0 + k) := Nat.mul_self_le_mul_self (Nat.le_add_right _ _)
    have h2 : n0 * n0 ≤ (n0 + (k + 1)) * (n0 + (k + 1)) := Nat.mul_self_le_mul_self (Nat.le_add_right _ _)
    apply Nat.cast_injective (R := ℤ)
    push_cast [Nat.cast_sub h1, Nat.cast_sub h2]
    ring

section lf
variable {φ : ℝ} (hφ : 1 < φ) (hφE : φ = (P.f : ℝ) / P.e)
include hφE

/-- **the L group**: `k` unit theta strips tile `{y <= k, x + y <= s}`, `b (s^2 - (s-k)^2)` tiles -/
def lFam : TFam (Phi φ '' slReg (P.e : ℝ) P.f P.j P.s) (Mrow hφ P.e P.f P.he0 P.hef) (P.b * (P.s * P.s - P.n0 * P.n0)) := by
  have H := P.rh
  have hE := H.hE
  have hEF := H.hEF
  obtain ⟨hF, hB, hEF', hv, hm0, hj0⟩ := H.pos
  let R : ∀ i : Fin P.kk, TFam (Phi φ '' bandReg (P.e : ℝ) P.f (((P.n0 + (i : ℕ) : ℕ) : ℝ))) (Mrow hφ P.e P.f P.he0 P.hef)
      (P.b * (2 * (P.n0 + (i : ℕ)) + 1)) := fun i =>
    castTF rfl (strip_cnt P.e P.f P.b (P.n0 + i) P.hef P.hb (P.strip_hg i)) (stripFam hφ P.e P.f P.b (P.n0 + i) P.he0 P.hef P.hb hφE (P.strip_hg i))
  have hcnt : (∑ i : Fin P.kk, P.b * (2 * (P.n0 + (i : ℕ)) + 1)) = P.b * (P.s * P.s - P.n0 * P.n0) := by
    rw [P.sum_strips P.kk P.n0, P.n0_add]
  refine castTF rfl hcnt (TFam.join (m := P.kk) (Phi φ '' slReg (P.e : ℝ) P.f P.j P.s)
    (fun i => Phi φ '' bandReg (P.e : ℝ) P.f (((P.n0 + (i : ℕ) : ℕ) : ℝ))) _ R ?_ ?_)
  · intro i
    refine Set.image_mono (band_sub (P.s : ℝ) _ (P.j : ℝ) hE hEF ?_ ?_)
    · have : P.n0 + (i : ℕ) + 1 ≤ P.s := by have := i.2; have := P.n0_add; unfold kk at *; omega
      exact_mod_cast this
    · have h2 : P.s = P.n0 + P.j * P.f := by have := P.n0_add; unfold kk at this; omega
      have : (P.s : ℝ) - P.j * P.f ≤ ((P.n0 + (i : ℕ) : ℕ) : ℝ) := by
        have : (P.s : ℝ) = P.n0 + P.j * P.f := by exact_mod_cast h2
        push_cast; have := (Nat.cast_nonneg (i : ℕ) : (0 : ℝ) ≤ ((i : ℕ) : ℝ)); linarith
      exact this
  · intro i j hij
    have hi := i.2; have hj := j.2
    have hne : (i : ℕ) ≠ (j : ℕ) := fun h => hij (Fin.ext h)
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · refine disjoint_image hφ (bands_disj hE hEF _ _ ?_)
      have : P.n0 + (i : ℕ) + 1 ≤ P.n0 + (j : ℕ) := by omega
      exact_mod_cast this
    · refine (disjoint_image hφ (bands_disj hE hEF _ _ ?_)).symm
      have : P.n0 + (j : ℕ) + 1 ≤ P.n0 + (i : ℕ) := by omega
      exact_mod_cast this

end lf

end NP

end

end Erdos634.Draft.ThetaNotch
