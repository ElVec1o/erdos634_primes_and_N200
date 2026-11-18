-- Draft/ThetaOddECol.lean -- ODD-E formalization, module 9: the column gadget of Theorem B (pieces G, T1, B and an optional corner triangle T0).
-- INTERNAL BUILD ONLY, UNAUDITED beyond internal checks.  No sorry, no native_decide.
/-
Column of chart width `L = e lambda` at `u = u0` (RESULT.md S2, B.2: P2-P4 for `lambda = n`, `u0 = 0`; P5-P8 for `lambda = 1`, `u0 = en + (i-1)e`):
  T0 : triangle {U >= 0, v >= 0, U + v <= L}             (scale e lambda; absent in the left column, replaced by an empty family)
  G  : green parallelogram {0 <= U <= L, L <= U + v <= L + mu}   (f lambda x m cells; h-side L c / a, v-side m c)
  T1 : blue triangle {U <= L, v <= L + mu, U + v >= L + mu}      (scale L)
  B  : blue rows [0,L] x [L+mu, V1]                              (L x R cells)
with `U = u - u0`, `mu = m c / a = m f / e`, `V1 = L + mu + R`.  Credit: the AI assistant's Theorem B; Beeson-Rosu (cells); the project.
INTERNAL BUILD ONLY, UNAUDITED beyond internal checks.
-/
import Erdos634.Draft.ThetaOddEPiece

open scoped Classical
open Erdos634.Geometry Erdos634.CertCoord

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Erdos634.Draft.ThetaNotch
noncomputable section
open Erdos634.Draft.WFrameF Erdos634.Draft.RegionTiling Erdos634.Draft.WBrickF Erdos634.Draft.CollarLayer
open Erdos634.Draft.LadderFam Erdos634.Draft.CollarFam

/-- the empty `HP` with a prescribed box -/
def emptyHP {φ : ℝ} {Mt : Erdos634.Geometry.Tri} {E F s M K : ℝ} (bx : OBx) : HPs φ Mt E F s M K bx 0 :=
  ⟨⟨bx, 0, ∅, castTF (by simp) rfl (TFam.emptyN (S := (∅ : Set Plane)) rfl), Set.empty_subset _⟩, rfl, rfl⟩

def castHPs {φ : ℝ} {Mt : Erdos634.Geometry.Tri} {E F s M K : ℝ} {bx : OBx} {n n' : ℕ} (P : HPs φ Mt E F s M K bx n) (h : n = n') :
    HPs φ Mt E F s M K bx n' := ⟨P.1, P.2.1, P.2.2.trans h⟩

section col
variable {φ : ℝ} (hφ : 1 < φ) (e f : ℕ) (he : 0 < e) (hef : e < f) (hφE : φ = (f : ℝ) / e)

/-- the green parallelogram `G` -/
def gPiece (s M K mu : ℝ) (m : ℕ) (hmu : mu = (m : ℝ) * f / e) (ac ca : ℝ) (hac : ac = (e : ℝ) * f / (f : ℝ) ^ 2)
    (hca : ca = (f : ℝ) ^ 2 / ((e : ℝ) * f)) (u0 : ℝ) (lam : ℕ) (hl : 0 < lam) :
    HPs φ (Mrow hφ e f he hef) (e : ℝ) f s M K ⟨u0, u0 + ((e * lam : ℕ) : ℝ), 0, ((e * lam : ℕ) : ℝ) + mu,
      u0 + ((e * lam : ℕ) : ℝ), u0 + ((e * lam : ℕ) : ℝ) + mu⟩ (2 * (f * lam) * m) := by
  have hE : (0 : ℝ) < e := by exact_mod_cast he
  have hEF : (e : ℝ) < f := by exact_mod_cast hef
  have hF : (0 : ℝ) < f := by linarith
  set L : ℝ := ((e * lam : ℕ) : ℝ) with hLdef
  have hL : 0 < L := by rw [hLdef]; exact_mod_cast Nat.mul_pos he hl
  have hmu0 : 0 ≤ mu := by rw [hmu]; positivity
  have hacne : ac ≠ 0 := by rw [hac]; positivity
  have hpa : ((f * lam : ℕ) : ℝ) * ac = L := by
    rw [hLdef, hac]; push_cast; field_simp
  have hqc : (m : ℝ) * ca = mu := by rw [hca, hmu]; field_simp
  have hacca : ac * ca = 1 := by rw [hac, hca]; field_simp
  refine parPiece hφ e f he hef hφE s M K (u0 + L) 0 (-ac) ac 0 ca (f * lam) m
    ⟨u0, u0 + L, 0, L + mu, u0 + L, u0 + L + mu⟩ (by intro h; nlinarith [hacca])
    (((e : ℝ) * f) ^ 2) (((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ^ 2) (((f : ℝ) ^ 2) ^ 2)
    (by unfold Qc; rw [hac]; field_simp; ring)
    (by unfold Qc; rw [hac, hca]; field_simp; ring)
    (by unfold Qc; rw [hca]; field_simp; ring)
    (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))) ?_
  intro hp hq
  refine ⟨?_, ?_, ?_, ?_⟩ <;> refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

/-- the blue triangle `T1` -/
def t1Piece (s M K mu : ℝ) (hmu0 : 0 ≤ mu) (u0 : ℝ) (lam : ℕ) (hl : 0 < lam) :
    HPs φ (Mrow hφ e f he hef) (e : ℝ) f s M K ⟨u0, u0 + ((e * lam : ℕ) : ℝ), mu, ((e * lam : ℕ) : ℝ) + mu,
      u0 + ((e * lam : ℕ) : ℝ) + mu, u0 + 2 * ((e * lam : ℕ) : ℝ) + mu⟩ ((e * lam) * (e * lam)) := by
  set L : ℝ := ((e * lam : ℕ) : ℝ) with hLdef
  have hL : 0 < L := by rw [hLdef]; exact_mod_cast Nat.mul_pos he hl
  refine triPiece hφ e f he hef hφE s M K (u0 + L) (L + mu) u0 (L + mu) (u0 + L) mu (e * lam) (Nat.mul_pos he hl)
    ⟨u0, u0 + L, mu, L + mu, u0 + L + mu, u0 + 2 * L + mu⟩ (by nlinarith)
    (((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ^ 2) (((f : ℝ) ^ 2) ^ 2) (((e : ℝ) * f) ^ 2)
    (by unfold Qc; rw [hLdef]; ring) (by unfold Qc; rw [hLdef]; ring) (by unfold Qc; rw [hLdef]; ring)
    (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)) ?_
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩ <;> linarith

/-- the blue rows `B` -/
def bPiece (s M K mu : ℝ) (hmu0 : 0 ≤ mu) (u0 : ℝ) (lam : ℕ) (hl : 0 < lam) (R : ℕ) (V1 : ℝ)
    (hV1 : V1 = ((e * lam : ℕ) : ℝ) + mu + R) :
    HPs φ (Mrow hφ e f he hef) (e : ℝ) f s M K ⟨u0, u0 + ((e * lam : ℕ) : ℝ), ((e * lam : ℕ) : ℝ) + mu, V1,
      u0 + ((e * lam : ℕ) : ℝ) + mu, u0 + ((e * lam : ℕ) : ℝ) + V1⟩ (2 * (e * lam) * R) := by
  set L : ℝ := ((e * lam : ℕ) : ℝ) with hLdef
  have hL : 0 < L := by rw [hLdef]; exact_mod_cast Nat.mul_pos he hl
  have hR0 : (0 : ℝ) ≤ R := Nat.cast_nonneg R
  refine parPiece hφ e f he hef hφE s M K u0 (L + mu) 1 0 0 1 (e * lam) R
    ⟨u0, u0 + L, L + mu, V1, u0 + L + mu, u0 + L + V1⟩ (by norm_num)
    (((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ^ 2) (((f : ℝ) ^ 2) ^ 2) (((e : ℝ) * f) ^ 2)
    (by unfold Qc; ring) (by unfold Qc; ring) (by unfold Qc; ring)
    (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)) ?_
  intro hp hq
  refine ⟨?_, ?_, ?_, ?_⟩ <;> refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> nlinarith

end col

end

end Erdos634.Draft.ThetaNotch
