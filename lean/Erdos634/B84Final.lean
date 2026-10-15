import Erdos634.BADFinal2
import Erdos634.B84Geom

/-!
# `BADL2.theoremA_L2_full` instantiated on a real dissection (N = 84), and a control

`Hyp e f X Y D` is, verbatim, the hypothesis list of
`theoremA_L2_full` (after `D`, `e`, `f`, `X`, `Y`).  `witness84`: `∃ D : CongruentDissection 84, Hyp 1 2 24 42 D`
(built in `B84Geom`: the cevian union of the 48-tile atom `A_4` and a 36-tile scaled tile).
`theoremA_at_84`: the theorem applied to it.  `control_13`: `Hyp 1 3 X Y D` is impossible for any
dissection whose model has sides `2,3,4` (it demands a model side `f²-e² = 8`).
-/

namespace Erdos634.B84
open Erdos634.Geometry Erdos634.BADL2
open Erdos634.Draft.FDBBaseBetaE1 (HasSides)

noncomputable section

def Hyp {N : ℕ} (e f : ℤ) (X Y : ℝ) (D : CongruentDissection N) : Prop :=
  ∃ σ τ : Equiv.Perm (Fin 3),
    D.model.oppLen (σ 0) = (e : ℝ) * f ∧
    D.model.oppLen (σ 1) = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 ∧
    D.model.oppLen (σ 2) = (f : ℝ) ^ 2 ∧
    D.target.angleAt (τ 0) = D.model.angleAt (σ 0) ∧
    D.target.angleAt (τ 1) = D.model.angleAt (σ 0) ∧
    D.target.oppLen (τ 0) = X ∧ D.target.oppLen (τ 1) = X ∧ D.target.oppLen (τ 2) = Y

theorem apply_full {N : ℕ} (D : CongruentDissection N) (e f : ℤ) (h0 : 0 < e) (hef : e < f)
    (hcop : IsCoprime e f) (X Y : ℝ) (h : Hyp e f X Y D) :
    ∃ w : ℤ, X = (f : ℝ) ^ 2 * w ∧ Y = (2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2) * w ∧ (f ^ 2 - e ^ 2) ∣ w := by
  obtain ⟨σ, τ, l0, l1, l2, a0, a1, m0, m1, m2⟩ := h
  exact theoremA_L2_full D e f h0 hef hcop X Y σ l0 l1 l2 τ a0 a1 m0 m1 m2

theorem opp_of_hasSides (T : Tri) {a b c : ℝ} (h : HasSides T a b c) :
    ∃ ρ : Equiv.Perm (Fin 3), T.oppLen (ρ 0) = a ∧ T.oppLen (ρ 1) = b ∧ T.oppLen (ρ 2) = c := by
  obtain ⟨ρ, h1, h2, h3⟩ := h
  refine ⟨ρ, ?_, ?_, ?_⟩
  · rw [← relabel_opp]; first | exact h1 | simpa [Tri.oppLen] using h1
  · rw [← relabel_opp]; first | exact h2 | simpa [Tri.oppLen] using h2
  · rw [← relabel_opp]; first | exact h3 | simpa [Tri.oppLen] using h3

theorem opp_mem (T : Tri) (h : HasSides T 2 3 4) (k : Fin 3) :
    T.oppLen k = 2 ∨ T.oppLen k = 3 ∨ T.oppLen k = 4 := by
  obtain ⟨ρ, a, b, c⟩ := opp_of_hasSides T h
  obtain ⟨j, rfl⟩ := ρ.surjective k
  fin_cases j
  · left; first | exact a | simpa using a
  · right; left; first | exact b | simpa using b
  · right; right; first | exact c | simpa using c

/-- **The witness.** -/
theorem witness84 : ∃ D : CongruentDissection 84, Hyp 1 2 24 42 D := by
  obtain ⟨D, hm, h1, h2, h3⟩ := b84_exists
  obtain ⟨ρ, l0, l1, l2⟩ := opp_of_hasSides D.model hm
  have e0 : D.target.oppLen 0 = 24 := h1
  have e1 : D.target.oppLen 1 = 24 := h2
  have e2 : D.target.oppLen 2 = 42 := h3
  obtain ⟨hcα, -, -, -⟩ := tile_angles D.model ρ 1 2 (by norm_num) (by norm_num)
    (by rw [l0]; norm_num) (by rw [l1]; norm_num) (by rw [l2]; norm_num)
  have hc : Real.cos (D.model.angleAt (ρ 0)) = 7 / 8 := by rw [hcα]; norm_num
  obtain ⟨c0, c1, -⟩ := cos_laws D.target
  rw [e0, e1, e2] at c0 c1
  have t0 : Real.cos (D.target.angleAt 0) = 7 / 8 := by linarith
  have t1 : Real.cos (D.target.angleAt 1) = 7 / 8 := by linarith
  obtain ⟨m0, m1⟩ := ang_bounds D.model (ρ 0)
  obtain ⟨p0, p1⟩ := ang_bounds D.target 0
  obtain ⟨q0, q1⟩ := ang_bounds D.target 1
  refine ⟨D, ρ, Equiv.refl _, ?_, ?_, ?_, ?_, ?_, e0, e1, e2⟩
  · rw [l0]; norm_num
  · rw [l1]; norm_num
  · rw [l2]; norm_num
  · exact Real.injOn_cos ⟨p0, p1⟩ ⟨m0, m1⟩ (by rw [t0, hc])
  · exact Real.injOn_cos ⟨q0, q1⟩ ⟨m0, m1⟩ (by rw [t1, hc])

/-- **Theorem A on a real object**: `X = 24 = f² w`, `Y = 42 = (2f²-e²) w`, `3 ∣ w` (so `w = 6`). -/
theorem theoremA_at_84 : ∃ D : CongruentDissection 84, Hyp 1 2 24 42 D ∧
    ∃ w : ℤ, (24 : ℝ) = (2 : ℝ) ^ 2 * w ∧ (42 : ℝ) = (2 * (2 : ℝ) ^ 2 - 1 ^ 2) * w ∧
      ((2 : ℤ) ^ 2 - 1 ^ 2) ∣ w := by
  obtain ⟨D, h⟩ := witness84
  obtain ⟨w, h1, h2, h3⟩ := apply_full D 1 2 (by norm_num) (by norm_num) (by norm_num) 24 42 h
  exact ⟨D, h, w, by simpa using h1, by simpa using h2, h3⟩

/-- **Control**: with the `(e,f) = (1,3)` data (model sides `(3, 8, 9)`) the hypotheses are
unsatisfiable by every dissection whose model has sides `2,3,4`, in particular by the 84 one. -/
theorem control_13 {N : ℕ} (D : CongruentDissection N) (hm : HasSides D.model 2 3 4)
    (X Y : ℝ) : ¬ Hyp 1 3 X Y D := by
  rintro ⟨σ, τ, l0, l1, l2, -⟩
  rcases opp_mem D.model hm (σ 1) with h | h | h <;>
  · rw [l1] at h; norm_num at h

/-- The control applies to the actual witness: the 84 dissection has model sides `2,3,4`. -/
theorem control_13_at_84 : ∃ D : CongruentDissection 84, HasSides D.model 2 3 4 ∧
    ∀ X Y : ℝ, ¬ Hyp 1 3 X Y D := by
  obtain ⟨D, hm, -⟩ := b84_exists
  exact ⟨D, hm, control_13 D hm⟩

end

end Erdos634.B84

#print axioms Erdos634.B84.witness84
#print axioms Erdos634.B84.theoremA_at_84
#print axioms Erdos634.B84.control_13_at_84
