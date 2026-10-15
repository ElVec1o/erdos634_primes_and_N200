import Erdos634.BADGridChar

namespace Erdos634.Draft.BADGridCharWrap

open LaurentPolynomial
open Erdos634.BADL2
open Erdos634.Geometry

noncomputable section

/-- Delegation: `ofAddChar_chi` — the character value on lattice elements. -/
theorem wrap_ofAddChar_chi {A R : Type*} [AddCommGroup A] [CommRing R]
    (φ : A →+ Real.Angle) (ψ0 : AddChar A R)
    (hker : ∀ a, φ a = 0 → ψ0 a = 1) (a₀ : A)
    (hπ : φ a₀ = ((Real.pi : ℝ) : Real.Angle)) (hψ : ψ0 a₀ = -1)
    (anchor : Real.Angle) (a : A) :
    (ofAddChar φ ψ0 hker a₀ hπ hψ anchor).chi (φ a) = ψ0 a :=
  ofAddChar_chi φ ψ0 hker a₀ hπ hψ anchor a

/-- Delegation: `psi0_apply` — concrete formula for `psi0 (i, j)`. -/
theorem wrap_psi0_apply (i j : ℤ) :
    psi0 (i, j) = C ((BAD.ee i j : ℤ) : ℝ) * T (BAD.kk i j) :=
  psi0_apply i j

/-- Delegation: `psi0_ker` — `psi0` kills the kernel of `phi α β`. -/
theorem wrap_psi0_ker (α β : ℝ) (hα : ¬∃ r : ℚ, α = r * Real.pi)
    (hβ : 3 * α + 2 * β = Real.pi) (p : ℤ × ℤ) (h : phi α β p = 0) :
    psi0 p = 1 :=
  psi0_ker α β hα hβ p h

example : True := trivial

#print axioms wrap_psi0_ker

end

end Erdos634.Draft.BADGridCharWrap
