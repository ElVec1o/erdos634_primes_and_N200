import Erdos634.BADAlgebra

namespace Erdos634.Draft.BADAlgebraWrap

open LaurentPolynomial
open BAD

/-- Delegation: `tsum_eq` — every signed shifted-tile sum factors through `Phi`. -/
theorem wrap_tsum_eq (e f : ℤ) (l : List (ℤ × ℤ × Bool)) :
    tsum e f l = Phi e f * gsum e f l :=
  tsum_eq e f l

/-- Delegation: `Phi_ne_zero`. -/
theorem wrap_Phi_ne_zero (e f : ℤ) (h0 : 0 < e) (hef : e < f) : Phi e f ≠ 0 :=
  Phi_ne_zero e f h0 hef

/-- Delegation: `basealpha_div_of_poly` — the key divisibility conclusion. -/
theorem wrap_basealpha_div_of_poly (e f w : ℤ) (h0 : 0 < e) (hef : e < f)
    (hcb : IsCoprime e (f ^ 2 - e ^ 2)) (hcf : IsCoprime f (f ^ 2 - e ^ 2))
    (l : List (ℤ × ℤ × Bool)) (h : Bdry e f w = tsum e f l) : (f ^ 2 - e ^ 2) ∣ w :=
  basealpha_div_of_poly e f w h0 hef hcb hcf l h

example : True := trivial

#print axioms wrap_basealpha_div_of_poly

end Erdos634.Draft.BADAlgebraWrap
