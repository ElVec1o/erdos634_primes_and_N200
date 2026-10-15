import Erdos634.ATDAlg
import Erdos634.BADL2

/-!
# ATD layer L2: the ATOM target flux and the dissection-level polynomial identity  Target: a triangle with angles `α+β` at vertices 0,1 (sides opposite:
`X`, `X`) and third side `Y` (apex, angle `α` by the angle sum).  Its anchored flux in `ℝ[T;T⁻¹]` is
`Y - X t - X t⁻¹` (both orientations; `chi(π-(α+β)) = ψ0(2,1) = -t`, `chi(π-α) = t⁻²`).
`L2atom`: for a `CongruentDissection` with model `(ef, f²-e², f²)`, `Y - X(t+t⁻¹)` is a signed sum
of shifted tile polynomials, with integer `(X,Y)`.
-/

open LaurentPolynomial

namespace Erdos634.ATDL2
open Erdos634.Geometry Erdos634.BADL2

noncomputable section

def Qa (X Y : ℝ) : LR := C Y - C X * T 1 - C X * T (-1)

theorem Qa_eq (X Y : ℝ) : Qa X Y = C Y + C (-X) * T 1 + C (-X) * T (-1) := by
  simp only [Qa, map_neg]; ring

theorem Qa_coeff0 (X Y : ℝ) : Qa X Y 0 = Y := by
  rw [Qa_eq]
  simp [← single_eq_C_mul_T, Finsupp.single_apply]

theorem Qa_coeff1 (X Y : ℝ) : Qa X Y 1 = -X := by
  rw [Qa_eq]
  simp [← single_eq_C_mul_T, Finsupp.single_apply]

theorem mp_BaXY (X Y : ℤ) : mp (ATD.BaXY X Y) = Qa (X : ℝ) (Y : ℝ) := by
  simp only [ATD.BaXY, Qa, map_sub, map_mul, mp_C, mp_T]

theorem ee21 : BAD.ee 2 1 = -1 := by
  have : BAD.ee 2 1 = BAD.ee 3 2 := by unfold BAD.ee; norm_num
  rw [this]; exact BAD.ee32'

theorem target_flux_atom (α β : ℝ) (hα : ¬∃ r : ℚ, α = r * Real.pi) (hβ : 3 * α + 2 * β = Real.pi)
    (X Y : ℝ) (Tt : Tri) (h0 : Tt.angleAt 0 = α + β) (h1 : Tt.angleAt 1 = α + β)
    (l0 : Tt.oppLen 0 = X) (l1 : Tt.oppLen 1 = X) (l2 : Tt.oppLen 2 = Y) :
    Tt.flux (gc α β hα hβ (Tt.leftUnit 0).angle).weight = Qa X Y := by
  set G := gc α β hα hβ (Tt.leftUnit 0).angle with hG
  have hsum := Tt.angleAt_sum
  have h2 : Tt.angleAt 2 = α := by linarith
  have hA : ((Tt.angleAt 0 : ℝ) : Real.Angle) ∈ G.L := by
    rw [h0]; exact mem_coord α β hα hβ _ 1 1 _ (by push_cast; ring)
  have hB : ((Tt.angleAt 1 : ℝ) : Real.Angle) ∈ G.L := by
    rw [h1]; exact mem_coord α β hα hβ _ 1 1 _ (by push_cast; ring)
  have hC : ((Tt.angleAt 2 : ℝ) : Real.Angle) ∈ G.L := by
    rw [h2]; exact mem_coord α β hα hβ _ 1 0 _ (by simp)
  have hL : ∀ k, ((Tt.angleAt k : ℝ) : Real.Angle) ∈ G.L := by
    intro k
    fin_cases k
    exacts [hA, hB, hC]
  have c1 : G.chi ((Real.pi - Tt.angleAt 1 : ℝ) : Real.Angle) = -(T 1 : LR) := by
    rw [h1, chi_coord α β hα hβ _ 2 1 _ (by push_cast; linarith), psi0_apply, ee21]
    have k : BAD.kk 2 1 = 1 := by decide
    rw [k]; simp
  have c2 : G.chi ((Real.pi - Tt.angleAt 2 : ℝ) : Real.Angle) = T (-1) * T (-1) := by
    rw [h2]; exact chi_Ang α β hα hβ _ 0
  have w0 : G.weight (Tt.leftUnit 0) = 1 := G.val_anchor
  have hu : (T 1 : LR) * T (-1) = 1 := T1_mul
  have cX : ∀ r : ℝ, algebraMap ℝ LR r = C r := fun r => (LaurentPolynomial.C_eq_algebraMap r).symm
  rcases Tt.det_pos_or_neg with hT | hT
  · rw [flux_pos_R G Tt hT hL, w0, c1, c2, cX, cX, cX, l0, l1, l2]
    unfold Qa
    linear_combination (-(C X * T (-1))) * hu
  · rw [flux_neg_R G Tt hT hL, c1, c2, cX, cX, cX, l0, l1, l2]
    have H := w0_neg G Tt hT hL
    rw [w0, c1, c2] at H
    set w2 := G.weight (Tt.leftUnit 2)
    have hw2 : w2 = -(T 1 : LR) := by
      linear_combination (T 1 : LR) * H - w2 * (T 1 * T (-1) + 1) * hu
    rw [hw2]
    unfold Qa
    linear_combination (-(C X * T (-1)) + C Y * (T 1 * T (-1) + 1)) * hu

theorem L2atom {N : ℕ} (D : CongruentDissection N) (e f : ℤ) (α β : ℝ)
    (hα : ¬∃ r : ℚ, α = r * Real.pi) (hβ : 3 * α + 2 * β = Real.pi)
    (hmodel : ∃ σ : Equiv.Perm (Fin 3),
      D.model.angleAt (σ 0) = α ∧ D.model.oppLen (σ 0) = (e : ℝ) * f ∧
      D.model.angleAt (σ 1) = β ∧ D.model.oppLen (σ 1) = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 ∧
      D.model.angleAt (σ 2) = Real.pi - α - β ∧ D.model.oppLen (σ 2) = (f : ℝ) ^ 2)
    (X Y : ℝ)
    (htgt : D.target.angleAt 0 = α + β ∧ D.target.angleAt 1 = α + β ∧ D.target.oppLen 0 = X ∧
      D.target.oppLen 1 = X ∧ D.target.oppLen 2 = Y) :
    ∃ (X' Y' : ℤ) (l : List (ℤ × ℤ × Bool)), X = X' ∧ Y = Y' ∧ ATD.BaXY X' Y' = BAD.tsum e f l := by
  obtain ⟨ρ, hρ⟩ := model_perm D e f α β hmodel
  obtain ⟨t0, t1, t2, t3, t4⟩ := htgt
  set anchor := (D.target.leftUnit 0).angle with hanc
  have hcancel := D.flux_cancel (E := LR) (gc α β hα hβ anchor).weight
    (gc α β hα hβ anchor).weight_odd
  have hT := target_flux_atom α β hα hβ X Y D.target t0 t1 t2 t3 t4
  have htile : ∀ i : Fin N, ∃ (σ s : ℤ) (bb : Bool),
      (D.tile i).flux (gc α β hα hβ anchor).weight = mp (BAD.term e f (σ, s, bb)) := by
    intro i
    obtain ⟨τ, hτ⟩ := (D.tiles_congruent i).exists_perm
    refine tile_flux_form α β hα hβ anchor e f (D.tile i) (τ.trans ρ) ?_ ?_
    · intro k; rw [(hτ k).1, (hρ (τ k)).1]; rfl
    · intro k; rw [(hτ k).2, (hρ (τ k)).2]; rfl
  choose σ s bb hfl using htile
  let g : Fin N → ℤ × ℤ × Bool := fun i => (σ i, s i, bb i)
  have hsum : mp (BAD.tsum e f (List.ofFn g)) = Qa X Y := by
    rw [tsum_ofFn]
    have : ∀ i, mp (BAD.term e f (g i)) = (D.tile i).flux (gc α β hα hβ anchor).weight :=
      fun i => (hfl i).symm
    rw [Finset.sum_congr rfl fun i _ => this i, hcancel, hT]
  set q := BAD.tsum e f (List.ofFn g) with hq
  have hX1 : ((q 1 : ℤ) : ℝ) = -X := by rw [← mp_coeff, hsum, Qa_coeff1]
  have hY : Y = ((q 0 : ℤ) : ℝ) := by rw [← mp_coeff, hsum, Qa_coeff0]
  have hX : X = (((-(q 1)) : ℤ) : ℝ) := by push_cast; linarith
  refine ⟨-(q 1), q 0, List.ofFn g, hX, hY, ?_⟩
  apply mp_injective
  rw [mp_BaXY, ← hX, ← hY]
  exact hsum.symm

end

end Erdos634.ATDL2

#print axioms Erdos634.ATDL2.target_flux_atom
#print axioms Erdos634.ATDL2.L2atom
