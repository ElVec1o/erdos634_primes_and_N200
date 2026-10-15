import Erdos634.BADL2

namespace Erdos634.Draft.BADL2Wrap

open Erdos634.BADL2 Erdos634.Geometry
open LaurentPolynomial BAD

theorem wrap_Bdry_eq_Bd (e f w : ℤ) :
    BAD.Bdry e f w = Bd (f ^ 2 * w) ((2 * f ^ 2 - e ^ 2) * w) :=
  Bdry_eq_Bd e f w

theorem wrap_Qv_coeff2 (X Y : ℝ) : Qv X Y 2 = X :=
  Qv_coeff2 X Y

theorem wrap_Qv_coeff0 (X Y : ℝ) : Qv X Y 0 = Y :=
  Qv_coeff0 X Y

theorem wrap_mp_Bd (X Y : ℤ) : mp (Bd X Y) = Qv (X : ℝ) (Y : ℝ) :=
  mp_Bd X Y

theorem wrap_L2 {N : ℕ} (D : CongruentDissection N) (e f : ℤ) (α β : ℝ)
    (hα : ¬∃ r : ℚ, α = r * Real.pi) (hβ : 3 * α + 2 * β = Real.pi)
    (hmodel : ∃ σ : Equiv.Perm (Fin 3),
      D.model.angleAt (σ 0) = α ∧ D.model.oppLen (σ 0) = (e : ℝ) * f ∧
      D.model.angleAt (σ 1) = β ∧ D.model.oppLen (σ 1) = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 ∧
      D.model.angleAt (σ 2) = Real.pi - α - β ∧ D.model.oppLen (σ 2) = (f : ℝ) ^ 2)
    (X Y : ℝ)
    (htgt : D.target.angleAt 0 = α ∧ D.target.angleAt 1 = α ∧ D.target.oppLen 0 = X ∧
      D.target.oppLen 1 = X ∧ D.target.oppLen 2 = Y) :
    ∃ (X' Y' : ℤ) (l : List (ℤ × ℤ × Bool)), X = X' ∧ Y = Y' ∧ Bd X' Y' = BAD.tsum e f l :=
  L2 D e f α β hα hβ hmodel X Y htgt

example : True := trivial
#print axioms Erdos634.BADL2.L2

end Erdos634.Draft.BADL2Wrap
