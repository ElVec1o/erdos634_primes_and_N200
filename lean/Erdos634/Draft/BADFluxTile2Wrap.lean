import Erdos634.BADFluxTile2

namespace Erdos634.Draft.BADFluxTile2Wrap

open LaurentPolynomial
open Erdos634.BADL2
open Erdos634.Geometry

noncomputable section

/-- Delegation: `phi_apply` — the angle homomorphism evaluated at `(i, j)`. -/
theorem wrap_phi_apply (α β : ℝ) (i j : ℤ) :
    phi α β (i, j) = (((i : ℝ) * α + (j : ℝ) * β : ℝ) : Real.Angle) :=
  phi_apply α β i j

/-- Delegation: `tile_flux_form` — every tile's flux is a `mp (BAD.term ...)`. -/
theorem wrap_tile_flux_form (α β : ℝ) (hα : ¬∃ r : ℚ, α = r * Real.pi)
    (hβ : 3 * α + 2 * β = Real.pi) (anchor : Real.Angle) (e f : ℤ) (Tt : Tri)
    (ρ : Equiv.Perm (Fin 3))
    (hang : ∀ k, Tt.angleAt k = Ang α β (ρ k))
    (hlen : ∀ k, Tt.oppLen k = Lenr e f (ρ k)) :
    ∃ (σ s : ℤ) (bb : Bool),
      Tt.flux (gc α β hα hβ anchor).weight = mp (BAD.term e f (σ, s, bb)) :=
  tile_flux_form α β hα hβ anchor e f Tt ρ hang hlen

example : True := trivial

#print axioms wrap_tile_flux_form

end

end Erdos634.Draft.BADFluxTile2Wrap
