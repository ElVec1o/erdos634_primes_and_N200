import Erdos634.BADPlacementGeo

namespace Erdos634.Draft.BADPlacementGeoWrap

open BAD

-- Re-exports: geometric link — complex-plane placements to directed-side lists

theorem wrap_rot_sides (ζ ω : ℂ) (hζ : ζ ≠ 0) (hω : ω ≠ 0)
    (a b c i j : ℤ) (A B C v : ℂ)
    (h1 : B - A = c) (h2 : C - B = a * (ζ ^ (3 : ℤ) * ω ^ (1 : ℤ)))
    (h3 : A - C = b * (ζ ^ (-2 : ℤ) * ω ^ (-2 : ℤ))) :
    HasCoord ζ ω ((ζ ^ i * ω ^ j * C + v) - (ζ ^ i * ω ^ j * B + v)) (a, i + 3, j + 1) ∧
    HasCoord ζ ω ((ζ ^ i * ω ^ j * B + v) - (ζ ^ i * ω ^ j * A + v)) (c, i, j) ∧
    HasCoord ζ ω ((ζ ^ i * ω ^ j * A + v) - (ζ ^ i * ω ^ j * C + v)) (b, i - 2, j - 2) :=
  rot_sides hζ hω a b c i j A B C v h1 h2 h3

theorem wrap_mir_sides (ζ ω : ℂ) (hζ : ζ ≠ 0) (hω : ω ≠ 0) (hrel : ζ ^ 3 * ω ^ 2 = -1)
    (hcζ : (starRingEnd ℂ) ζ = ζ⁻¹) (hcω : (starRingEnd ℂ) ω = ω⁻¹)
    (a b c i j : ℤ) (A B C v : ℂ)
    (h1 : B - A = c) (h2 : C - B = a * (ζ ^ (3 : ℤ) * ω ^ (1 : ℤ)))
    (h3 : A - C = b * (ζ ^ (-2 : ℤ) * ω ^ (-2 : ℤ))) :
    HasCoord ζ ω ((ζ ^ i * ω ^ j * (starRingEnd ℂ) C + v) -
        (ζ ^ i * ω ^ j * (starRingEnd ℂ) A + v)) (b, i + 5, j + 4) ∧
    HasCoord ζ ω ((ζ ^ i * ω ^ j * (starRingEnd ℂ) B + v) -
        (ζ ^ i * ω ^ j * (starRingEnd ℂ) C + v)) (a, i, j + 1) ∧
    HasCoord ζ ω ((ζ ^ i * ω ^ j * (starRingEnd ℂ) A + v) -
        (ζ ^ i * ω ^ j * (starRingEnd ℂ) B + v)) (c, i + 3, j + 2) :=
  mir_sides hζ hω hrel hcζ hcω a b c i j A B C v h1 h2 h3

example : True := trivial

#print axioms BAD.rot_sides
#print axioms BAD.mir_sides

end Erdos634.Draft.BADPlacementGeoWrap
