import Erdos634.ARAForm

namespace Erdos634.Draft.ARAFormWrap
open Erdos634.ARA
open Erdos634.Geometry

variable {N : ℕ}

/-- Heron value for the model triangle in (e,f) form. -/
theorem wrap_model_heron (D : CongruentDissection N) (e f : ℤ) (σ : Equiv.Perm (Fin 3))
    (l0 : D.model.oppLen (σ 0) = (e : ℝ) * f)
    (l1 : D.model.oppLen (σ 1) = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (l2 : D.model.oppLen (σ 2) = (f : ℝ) ^ 2) :
    Hh (D.model.oppLen 0) (D.model.oppLen 1) (D.model.oppLen 2) =
      (e : ℝ) ^ 2 * (4 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ^ 2 :=
  model_heron D e f σ l0 l1 l2

/-- N-form conclusion from Theorem A: N = r² (f²-e²)(2f²-e²). -/
theorem wrap_theoremA_N_form_full (D : CongruentDissection N) (e f : ℤ) (h0 : 0 < e)
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
    ∃ r : ℤ, (N : ℤ) = r ^ 2 * (f ^ 2 - e ^ 2) * (2 * f ^ 2 - e ^ 2) :=
  theoremA_N_form_full D e f h0 hef hcop X Y σ l0 l1 l2 τ a0 a1 m0 m1 m2

example : True := trivial

#print axioms wrap_theoremA_N_form_full

end Erdos634.Draft.ARAFormWrap
