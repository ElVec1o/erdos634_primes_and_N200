import Erdos634.BADTarget

namespace Erdos634.Draft.BADTargetWrap

open Erdos634.BADL2 Erdos634.Geometry
open LaurentPolynomial

theorem wrap_w0_neg {R : Type*} [CommRing R] (G : GridChar R) (T : Tri) (hT : T.det < 0)
    (h : ∀ k, ((T.angleAt k : ℝ) : Real.Angle) ∈ G.L) :
    G.weight (T.leftUnit 0) = G.chi ((Real.pi - T.angleAt 1 : ℝ) : Real.Angle)
      * (G.chi ((Real.pi - T.angleAt 2 : ℝ) : Real.Angle) * G.weight (T.leftUnit 2)) :=
  w0_neg G T hT h

theorem wrap_target_flux (α β : ℝ) (hα : ¬∃ r : ℚ, α = r * Real.pi)
    (hβ : 3 * α + 2 * β = Real.pi)
    (X Y : ℝ) (Tt : Tri) (h0 : Tt.angleAt 0 = α) (h1 : Tt.angleAt 1 = α)
    (l0 : Tt.oppLen 0 = X) (l1 : Tt.oppLen 1 = X) (l2 : Tt.oppLen 2 = Y) :
    Tt.flux (gc α β hα hβ (Tt.leftUnit 0).angle).weight
      = C Y + C X * (T 1 : LR) ^ 2 + C X * (T (-1) : LR) ^ 2 :=
  target_flux α β hα hβ X Y Tt h0 h1 l0 l1 l2

example : True := trivial
#print axioms Erdos634.BADL2.target_flux

end Erdos634.Draft.BADTargetWrap
