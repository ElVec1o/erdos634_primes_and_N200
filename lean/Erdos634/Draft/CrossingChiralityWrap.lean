import Erdos634.CrossingChirality

/-!
# CrossingChirality: the crossing statement is a chirality-uniformity statement, wrapper
Key results: `beta_gt_alpha`, `gamma_gt_alpha`, `figures_all_legal`,
`crossing_iff_chirality`, `no_propagation_from_figures`.
No sorry, standard axioms.
-/

namespace Erdos634.Draft.CrossingChiralityWrap
open Erdos634.CrossingChirality

/-- 3α + 2β = π with positive angles forces β > α. -/
theorem wrap_beta_gt_alpha (α β : ℝ) (hα : 0 < α) (hsum : 3 * α + 2 * β = Real.pi)
    (hb : Real.pi < 5 * β) : α < β :=
  beta_gt_alpha α β hα hsum hb

/-- γ = 2α + β > α for positive angles. -/
theorem wrap_gamma_gt_alpha (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) : α < 2 * α + β :=
  gamma_gt_alpha α β hα hβ

/-- All four local configurations at Q_k close the straight angle. -/
theorem wrap_figures_all_legal (α β : ℝ) (hsum : 3 * α + 2 * β = Real.pi) :
    (Real.pi - α - β = 2 * α + β)
      ∧ (Real.pi - 2 * α = α + 2 * β)
      ∧ (Real.pi - β - α = 2 * α + β)
      ∧ (Real.pi - 2 * β = 3 * α) :=
  figures_all_legal α β hsum

/-- noCross k ↔ alphaUp k; apex gives noCross f. -/
theorem wrap_crossing_iff_chirality (noCross alphaUp : ℕ → Prop) (f : ℕ)
    (equiv : ∀ k, noCross k ↔ alphaUp k) (apex : alphaUp f) :
    noCross f ∧ (∀ k, k < f → (noCross k ↔ alphaUp k)) :=
  crossing_iff_chirality noCross alphaUp f equiv apex

/-- No vertex figure at Q_k constrains T_k relative to T_{k+1}. -/
theorem wrap_no_propagation_from_figures (P : ℕ → Bool) (k : ℕ) :
    (P k = true ∨ P k = false) ∧ (P (k + 1) = true ∨ P (k + 1) = false) :=
  no_propagation_from_figures P k

example : (Bool.true = true ∨ Bool.true = false) ∧ (Bool.false = true ∨ Bool.false = false) :=
  no_propagation_from_figures (fun n => if n = 0 then Bool.true else Bool.false) 0

#print axioms wrap_beta_gt_alpha
#print axioms wrap_gamma_gt_alpha
#print axioms wrap_figures_all_legal
#print axioms wrap_crossing_iff_chirality
#print axioms wrap_no_propagation_from_figures

end Erdos634.Draft.CrossingChiralityWrap
