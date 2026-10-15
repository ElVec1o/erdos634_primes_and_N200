import Erdos634.ATDL2

namespace Erdos634.Draft.ATDL2Wrap
open Erdos634.ATDL2
open LaurentPolynomial
open Erdos634.Geometry Erdos634.BADL2

variable {N : ℕ}

/-- The target flux of the atom triangle equals the Qa polynomial. -/
theorem wrap_target_flux_atom (α β : ℝ) (hα : ¬∃ r : ℚ, α = r * Real.pi)
    (hβ : 3 * α + 2 * β = Real.pi)
    (X Y : ℝ) (Tt : Tri) (h0 : Tt.angleAt 0 = α + β) (h1 : Tt.angleAt 1 = α + β)
    (l0 : Tt.oppLen 0 = X) (l1 : Tt.oppLen 1 = X) (l2 : Tt.oppLen 2 = Y) :
    Tt.flux (gc α β hα hβ (Tt.leftUnit 0).angle).weight = Qa X Y :=
  target_flux_atom α β hα hβ X Y Tt h0 h1 l0 l1 l2

/-- L2 polynomial identity: for a congruent dissection with model (ef, f²-e², f²),
    the target's Y - X(t+t⁻¹) is a signed sum of shifted tile polynomials. -/
theorem wrap_L2atom (D : CongruentDissection N) (e f : ℤ) (α β : ℝ)
    (hα : ¬∃ r : ℚ, α = r * Real.pi) (hβ : 3 * α + 2 * β = Real.pi)
    (hmodel : ∃ σ : Equiv.Perm (Fin 3),
      D.model.angleAt (σ 0) = α ∧ D.model.oppLen (σ 0) = (e : ℝ) * f ∧
      D.model.angleAt (σ 1) = β ∧ D.model.oppLen (σ 1) = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 ∧
      D.model.angleAt (σ 2) = Real.pi - α - β ∧ D.model.oppLen (σ 2) = (f : ℝ) ^ 2)
    (X Y : ℝ)
    (htgt : D.target.angleAt 0 = α + β ∧ D.target.angleAt 1 = α + β ∧ D.target.oppLen 0 = X ∧
      D.target.oppLen 1 = X ∧ D.target.oppLen 2 = Y) :
    ∃ (X' Y' : ℤ) (l : List (ℤ × ℤ × Bool)), X = X' ∧ Y = Y' ∧
      ATD.BaXY X' Y' = BAD.tsum e f l :=
  L2atom D e f α β hα hβ hmodel X Y htgt

example : True := trivial

#print axioms wrap_L2atom

end Erdos634.Draft.ATDL2Wrap
