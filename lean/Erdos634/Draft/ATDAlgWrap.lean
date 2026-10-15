import Erdos634.ATDAlg

namespace Erdos634.Draft.ATDAlgWrap
open LaurentPolynomial ATD BAD

/-- Ba = Phi · (-μ t⁻¹): the boundary polynomial of the atom factors through the tile polynomial. -/
theorem wrap_Ba_eq (e f μ : ℤ) : Ba e f μ = Phi e f * (-(C μ * T (-1))) :=
  Ba_eq e f μ

/-- If Ba = tsum then (f²-e²) ∣ μ (algebraic core of atom divisibility). -/
theorem wrap_atomdiv_of_poly (e f μ : ℤ) (h0 : 0 < e) (hef : e < f)
    (hcb : IsCoprime e (f ^ 2 - e ^ 2))
    (l : List (ℤ × ℤ × Bool)) (h : Ba e f μ = tsum e f l) : (f ^ 2 - e ^ 2) ∣ μ :=
  atomdiv_of_poly e f μ h0 hef hcb l h

/-- Concrete check: Ba 1 2 12 = Phi 1 2 · (-12 t⁻¹). -/
theorem wrap_Ba_eq_12 : Ba 1 2 12 = Phi 1 2 * (-(C 12 * T (-1))) :=
  Ba_eq_12

example : True := trivial

#print axioms wrap_atomdiv_of_poly

end Erdos634.Draft.ATDAlgWrap
