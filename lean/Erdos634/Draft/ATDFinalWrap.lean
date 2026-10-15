import Erdos634.ATDFinal

namespace Erdos634.Draft.ATDFinalWrap
open Erdos634.ATDL2
open Erdos634.Geometry Erdos634.BADL2

variable {N : ℕ}

/-- Atom divisibility at the dissection level: X = f·μ, Y = e·μ, (f²-e²) ∣ μ. -/
theorem wrap_atomDiv_L2_full (D : CongruentDissection N) (e f : ℤ) (h0 : 0 < e) (hef : e < f)
    (hcop : IsCoprime e f) (X Y : ℝ)
    (σ : Equiv.Perm (Fin 3))
    (l0 : D.model.oppLen (σ 0) = (e : ℝ) * f)
    (l1 : D.model.oppLen (σ 1) = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (l2 : D.model.oppLen (σ 2) = (f : ℝ) ^ 2)
    (τ : Equiv.Perm (Fin 3))
    (a0 : D.target.angleAt (τ 0) = D.model.angleAt (σ 0) + D.model.angleAt (σ 1))
    (a1 : D.target.angleAt (τ 1) = D.model.angleAt (σ 0) + D.model.angleAt (σ 1))
    (m0 : D.target.oppLen (τ 0) = X) (m1 : D.target.oppLen (τ 1) = X)
    (m2 : D.target.oppLen (τ 2) = Y) :
    ∃ μ : ℤ, X = (f : ℝ) * μ ∧ Y = (e : ℝ) * μ ∧ (f ^ 2 - e ^ 2) ∣ μ :=
  atomDiv_L2_full D e f h0 hef hcop X Y σ l0 l1 l2 τ a0 a1 m0 m1 m2

/-- Integer corollary: if b·N = μ² and b ∣ μ then N = b·r². -/
theorem wrap_atom_count (b μ : ℤ) (n : ℕ) (hb : 0 < b) (hd : b ∣ μ) (harea : b * (n : ℤ) = μ ^ 2) :
    ∃ r : ℤ, (n : ℤ) = b * r ^ 2 :=
  atom_count b μ n hb hd harea

example : True := trivial

#print axioms wrap_atomDiv_L2_full

end Erdos634.Draft.ATDFinalWrap
