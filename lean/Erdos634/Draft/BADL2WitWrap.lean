import Erdos634.BADL2Wit

namespace Erdos634.Draft.BADL2WitWrap

open Erdos634.BADL2 Erdos634.Geometry Erdos634.Subdivision
open LaurentPolynomial BAD

-- Re-exports: witnesses and controls for layer L2

theorem wrap_alpha_witness_12 : ∃ α β : ℝ, (¬∃ r : ℚ, α = r * Real.pi) ∧
    3 * α + 2 * β = Real.pi ∧ Real.cos α = 7 / 8 :=
  alpha_witness_12

theorem wrap_psi0_witness :
    psi0 (6, 4) = 1 ∧ psi0 (3, 2) = -1 ∧
      psi0 (1, 0) = -(T 2 : LR) :=
  psi0_witness

theorem wrap_ladder_flux_instance (α β : ℝ) (hα : ¬∃ r : ℚ, α = r * Real.pi)
    (hβ : 3 * α + 2 * β = Real.pi) (anchor : Real.Angle)
    (A B C : Plane) (hindep : AffineIndependent ℝ ![A, B, C]) (k : ℕ) (hk : 0 < k) :
    ∑ i, ((Subdivision.ladderDissection A B C hindep k hk).tile i).flux
        (gc α β hα hβ anchor).weight
      = (Subdivision.ladderDissection A B C hindep k hk).target.flux
        (gc α β hα hβ anchor).weight :=
  ladder_flux_instance α β hα hβ anchor A B C hindep k hk

theorem wrap_poly_witness_and_control :
    BAD.Bdry 1 2 6 = BAD.tsum 1 2 [(6, -1, false), (8, -2, true), (-4, -2, false)] ∧
    (∀ l : List (ℤ × ℤ × Bool), BAD.Bdry 1 3 4 ≠ BAD.tsum 1 3 l) :=
  poly_witness_and_control

example : True := trivial

#print axioms Erdos634.BADL2.alpha_witness_12
#print axioms Erdos634.BADL2.poly_witness_and_control

end Erdos634.Draft.BADL2WitWrap
