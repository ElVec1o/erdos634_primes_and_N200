import Erdos634.BADFinal
import Erdos634.BADInstances
import Erdos634.CellCoord

/-!
# BAD layer L2: witnesses and controls

* `alpha_witness_12`: for the tile `(e,f) = (1,2)` the hypotheses `α/π irrational`, `3α+2β = π` of
  `gc`, `tile_flux_form`, `L2` are jointly satisfiable (`cos α = 7/8`, `sin(α/2) = 1/4`).
* `psi0_witness`: the character takes the claimed values (`ψ0(6,4)=1`, `ψ0(3,2)=-1`, `ψ0(1,0)=-T²`).
* `ladder_flux_instance`: the Laurent-valued weight `gc` is an admissible weight for
  `CongruentDissection.flux_cancel` on a real dissection (`Subdivision.ladderDissection`, `k²` tiles);
  this tests only the generic cancellation with `E = ℝ[T;T⁻¹]`, not an isosceles target.
* polynomial witness / control: `BAD.witness_84`, `BAD.control_34` (re-exported below).
-/

open LaurentPolynomial

namespace Erdos634.BADL2
open Erdos634.Geometry

noncomputable section

theorem alpha_witness_12 : ∃ α β : ℝ, (¬∃ r : ℚ, α = r * Real.pi) ∧ 3 * α + 2 * β = Real.pi ∧
    Real.cos α = 7 / 8 := by
  set α := Real.arccos (7 / 8) with hα
  have hc : Real.cos α = 7 / 8 := Real.cos_arccos (by norm_num) (by norm_num)
  have hb0 : 0 ≤ α := Real.arccos_nonneg _
  have hb1 : α ≤ Real.pi := Real.arccos_le_pi _
  refine ⟨α, (Real.pi - 3 * α) / 2, ?_, by ring, hc⟩
  have hsin : Real.sin (α / 2) = ((1 : ℕ) : ℝ) / (2 * ((2 : ℕ) : ℝ)) := by
    have h1 := Real.cos_two_mul (α / 2)
    have h2 := Real.sin_sq_add_cos_sq (α / 2)
    rw [show 2 * (α / 2) = α by ring, hc] at h1
    have hs : Real.sin (α / 2) ^ 2 = (1 / 4) ^ 2 := by nlinarith
    have hn : 0 ≤ Real.sin (α / 2) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
    have := (pow_left_inj₀ hn (by norm_num) (by norm_num)).mp hs
    rw [this]; norm_num
  exact Erdos634.BaseBetaE1.tile_alpha_irrational 1 2 le_rfl (by norm_num) α hsin

theorem psi0_witness :
    psi0 (6, 4) = 1 ∧ psi0 (3, 2) = -1 ∧
      psi0 (1, 0) = - (T 2 : LR) := by
  refine ⟨?_, psi0_pi, ?_⟩
  · rw [psi0_apply]
    have e : BAD.ee 6 4 = 1 := by decide
    have k : BAD.kk 6 4 = 0 := by decide
    rw [e, k]; simp
  · rw [psi0_apply]
    have e : BAD.ee 1 0 = -1 := by decide
    have k : BAD.kk 1 0 = 2 := by decide
    rw [e, k]; simp

/-- the Laurent weight is admissible for `flux_cancel` on a real dissection (generic part only). -/
theorem ladder_flux_instance (α β : ℝ) (hα : ¬∃ r : ℚ, α = r * Real.pi)
    (hβ : 3 * α + 2 * β = Real.pi) (anchor : Real.Angle)
    (A B C : Plane) (hindep : AffineIndependent ℝ ![A, B, C]) (k : ℕ) (hk : 0 < k) :
    ∑ i, ((Subdivision.ladderDissection A B C hindep k hk).tile i).flux
        (gc α β hα hβ anchor).weight
      = (Subdivision.ladderDissection A B C hindep k hk).target.flux
        (gc α β hα hβ anchor).weight :=
  (Subdivision.ladderDissection A B C hindep k hk).flux_cancel (E := LR)
    (gc α β hα hβ anchor).weight (gc α β hα hβ anchor).weight_odd

/-- polynomial-level witness and control (from `BADInstances`). -/
theorem poly_witness_and_control :
    BAD.Bdry 1 2 6 = BAD.tsum 1 2 [(6, -1, false), (8, -2, true), (-4, -2, false)] ∧
    (∀ l : List (ℤ × ℤ × Bool), BAD.Bdry 1 3 4 ≠ BAD.tsum 1 3 l) :=
  ⟨BAD.witness_84, BAD.control_34⟩

end

end Erdos634.BADL2

#print axioms Erdos634.BADL2.alpha_witness_12
#print axioms Erdos634.BADL2.psi0_witness
#print axioms Erdos634.BADL2.ladder_flux_instance
#print axioms Erdos634.BADL2.poly_witness_and_control
