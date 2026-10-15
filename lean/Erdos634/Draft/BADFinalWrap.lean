import Erdos634.BADFinal

namespace Erdos634.Draft.BADFinalWrap

open LaurentPolynomial
open Erdos634.BADL2
open Erdos634.Geometry Erdos634.NormalPosition

noncomputable section

/-- Delegation: `theoremA_L2` — the packed form of `prop:basealphadiv`. -/
theorem wrap_theoremA_L2 {N : ℕ} (D : CongruentDissection N) (e f w : ℤ) (h0 : 0 < e)
    (hef : e < f) (hcop : IsCoprime e f)
    (hmodel : ∃ σ : Equiv.Perm (Fin 3),
      D.model.oppLen (σ 0) = (e : ℝ) * f ∧
      D.model.oppLen (σ 1) = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 ∧
      D.model.oppLen (σ 2) = (f : ℝ) ^ 2)
    (htgt : ∃ τ : Equiv.Perm (Fin 3),
      D.target.oppLen (τ 0) = (f : ℝ) ^ 2 * w ∧
      D.target.oppLen (τ 1) = (f : ℝ) ^ 2 * w ∧
      D.target.oppLen (τ 2) = (2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2) * w) :
    (f ^ 2 - e ^ 2) ∣ w :=
  theoremA_L2 D e f w h0 hef hcop hmodel htgt

example : True := trivial

#print axioms wrap_theoremA_L2

end

end Erdos634.Draft.BADFinalWrap
