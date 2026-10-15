import Erdos634.BADFinal2

namespace Erdos634.Draft.BADFinal2Wrap

open LaurentPolynomial
open Erdos634.BADL2
open Erdos634.Geometry Erdos634.NormalPosition

noncomputable section

/-- Delegation: `theoremA_L2_full` — unpacked form with explicit permutations and angle equalities. -/
theorem wrap_theoremA_L2_full {N : ℕ} (D : CongruentDissection N) (e f : ℤ) (h0 : 0 < e)
    (hef : e < f) (hcop : IsCoprime e f) (X Y : ℝ)
    (σ : Equiv.Perm (Fin 3))
    (l0 : D.model.oppLen (σ 0) = (e : ℝ) * f)
    (l1 : D.model.oppLen (σ 1) = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (l2 : D.model.oppLen (σ 2) = (f : ℝ) ^ 2)
    (τ : Equiv.Perm (Fin 3))
    (a0 : D.target.angleAt (τ 0) = D.model.angleAt (σ 0))
    (a1 : D.target.angleAt (τ 1) = D.model.angleAt (σ 0))
    (m0 : D.target.oppLen (τ 0) = X) (m1 : D.target.oppLen (τ 1) = X)
    (m2 : D.target.oppLen (τ 2) = Y) :
    ∃ w : ℤ, X = (f : ℝ) ^ 2 * w ∧ Y = (2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2) * w ∧
      (f ^ 2 - e ^ 2) ∣ w :=
  theoremA_L2_full D e f h0 hef hcop X Y σ l0 l1 l2 τ a0 a1 m0 m1 m2

example : True := trivial

#print axioms wrap_theoremA_L2_full

end

end Erdos634.Draft.BADFinal2Wrap
