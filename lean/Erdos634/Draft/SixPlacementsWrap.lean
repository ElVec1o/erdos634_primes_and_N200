import Erdos634.SixPlacements

namespace Erdos634.Draft.SixPlacementsWrap
open Erdos634.SixPlacements Erdos634.Geometry

theorem wrap_six_placements {T M : Tri} (h : T.Congruent M) {a b c : ℝ}
    (hMa : dist (M.pts 0) (M.pts 1) = a) (hMb : dist (M.pts 1) (M.pts 2) = b)
    (hMc : dist (M.pts 0) (M.pts 2) = c)
    {v d : Plane} (hunit : d 0 ^ 2 + d 1 ^ 2 = 1)
    {k₀ k₁ k₂ : Fin 3} (h01 : k₀ ≠ k₁) (h02 : k₀ ≠ k₂) (h12 : k₁ ≠ k₂)
    (hk₀ : T.pts k₀ = v) {c' : ℝ} (hc' : 0 < c') (hk₁ : T.pts k₁ = v + c' • d)
    (hk₂ : 0 < cross d (T.pts k₂ - v)) :
    (T.pts k₁ = v + a • d ∧ T.pts k₂ = placeThird v d a c b) ∨
    (T.pts k₁ = v + c • d ∧ T.pts k₂ = placeThird v d c a b) ∨
    (T.pts k₁ = v + a • d ∧ T.pts k₂ = placeThird v d a b c) ∨
    (T.pts k₁ = v + b • d ∧ T.pts k₂ = placeThird v d b a c) ∨
    (T.pts k₁ = v + c • d ∧ T.pts k₂ = placeThird v d c b a) ∨
    (T.pts k₁ = v + b • d ∧ T.pts k₂ = placeThird v d b c a) :=
  six_placements h hMa hMb hMc hunit h01 h02 h12 hk₀ hc' hk₁ hk₂

example : True := trivial
#check @wrap_six_placements

end Erdos634.Draft.SixPlacementsWrap
