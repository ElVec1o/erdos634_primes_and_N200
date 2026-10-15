import Erdos634.BADFluxTile

namespace Erdos634.Draft.BADFluxTileWrap

open LaurentPolynomial
open Erdos634.BADL2
open Erdos634.Geometry

noncomputable section

/-- Delegation: `mp_injective` — the integer-to-real Laurent map is injective. -/
theorem wrap_mp_injective : Function.Injective mp :=
  mp_injective

/-- Delegation: `flux_pos_R` — flux of a positively-oriented tile. -/
theorem wrap_flux_pos_R {R : Type*} [CommRing R] [Algebra ℝ R] (G : GridChar R) (T : Tri)
    (hT : 0 < T.det) (h : ∀ k, ((T.angleAt k : ℝ) : Real.Angle) ∈ G.L) :
    T.flux G.weight = G.weight (T.leftUnit 0) *
      (algebraMap ℝ R (T.oppLen 2) +
        G.chi ((Real.pi - T.angleAt 1 : ℝ) : Real.Angle) * algebraMap ℝ R (T.oppLen 0) +
        G.chi ((Real.pi - T.angleAt 1 : ℝ) : Real.Angle) *
          G.chi ((Real.pi - T.angleAt 2 : ℝ) : Real.Angle) * algebraMap ℝ R (T.oppLen 1)) :=
  flux_pos_R G T hT h

example : True := trivial

#print axioms wrap_mp_injective

end

end Erdos634.Draft.BADFluxTileWrap
