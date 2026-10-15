import Erdos634.BADPlacementWit

namespace Erdos634.Draft.BADPlacementWitWrap

open BAD
open LaurentPolynomial

-- Re-exports: placed-tile polynomial witnesses and a wrong-shape counterexample

theorem wrap_placed_rot (ζ ω : ℂ) (hζ : ζ ≠ 0) (hω : ω ≠ 0)
    (e f i j : ℤ) (A B D v : ℂ)
    (h1 : B - A = ((f ^ 2 : ℤ) : ℂ))
    (h2 : D - B = ((e * f : ℤ) : ℂ) * (ζ ^ (3 : ℤ) * ω ^ (1 : ℤ)))
    (h3 : A - D = ((f ^ 2 - e ^ 2 : ℤ) : ℂ) * (ζ ^ (-2 : ℤ) * ω ^ (-2 : ℤ))) :
    ((HasCoord ζ ω ((ζ ^ i * ω ^ j * B + v) - (ζ ^ i * ω ^ j * A + v)) (f ^ 2, i, j)) ∧
     (HasCoord ζ ω ((ζ ^ i * ω ^ j * D + v) - (ζ ^ i * ω ^ j * B + v)) (e * f, i + 3, j + 1)) ∧
     (HasCoord ζ ω ((ζ ^ i * ω ^ j * A + v) - (ζ ^ i * ω ^ j * D + v))
        (f ^ 2 - e ^ 2, i - 2, j - 2))) ∧
    bp [(f ^ 2, i, j), (e * f, i + 3, j + 1), (f ^ 2 - e ^ 2, i - 2, j - 2)]
      = C (ee i j) * T (kk i j) * pTile e f :=
  placed_rot hζ hω e f i j A B D v h1 h2 h3

theorem wrap_placed_mir (ζ ω : ℂ) (hζ : ζ ≠ 0) (hω : ω ≠ 0)
    (hrel : ζ ^ 3 * ω ^ 2 = -1)
    (hcζ : (starRingEnd ℂ) ζ = ζ⁻¹) (hcω : (starRingEnd ℂ) ω = ω⁻¹)
    (e f i j : ℤ) (A B D v : ℂ)
    (h1 : B - A = ((f ^ 2 : ℤ) : ℂ))
    (h2 : D - B = ((e * f : ℤ) : ℂ) * (ζ ^ (3 : ℤ) * ω ^ (1 : ℤ)))
    (h3 : A - D = ((f ^ 2 - e ^ 2 : ℤ) : ℂ) * (ζ ^ (-2 : ℤ) * ω ^ (-2 : ℤ))) :
    ((HasCoord ζ ω ((ζ ^ i * ω ^ j * (starRingEnd ℂ) D + v) -
          (ζ ^ i * ω ^ j * (starRingEnd ℂ) A + v)) (f ^ 2 - e ^ 2, i + 5, j + 4)) ∧
     (HasCoord ζ ω ((ζ ^ i * ω ^ j * (starRingEnd ℂ) B + v) -
          (ζ ^ i * ω ^ j * (starRingEnd ℂ) D + v)) (e * f, i, j + 1)) ∧
     (HasCoord ζ ω ((ζ ^ i * ω ^ j * (starRingEnd ℂ) A + v) -
          (ζ ^ i * ω ^ j * (starRingEnd ℂ) B + v)) (f ^ 2, i + 3, j + 2))) ∧
    bp [(f ^ 2 - e ^ 2, i + 5, j + 4), (e * f, i, j + 1), (f ^ 2, i + 3, j + 2)]
      = C (-ee i j) * T (kk i j - 3) * qTile e f :=
  placed_mir hζ hω hrel hcζ hcω e f i j A B D v h1 h2 h3

theorem wrap_wit_rot :
    bp [(2 ^ 2, 1, -2), (1 * 2, 1 + 3, -2 + 1), (2 ^ 2 - 1 ^ 2, 1 - 2, -2 - 2)]
      = -(4 * T 8 + 3 * T 10 + 2 * T 11) :=
  wit_rot

theorem wrap_wit_mir :
    bp [(2 ^ 2 - 1 ^ 2, 2 + 5, 1 + 4), (1 * 2, 2, 1 + 1), (2 ^ 2, 2 + 3, 1 + 2)]
      = 3 * T (-1) + 2 * T (-2) + 4 * T 1 :=
  wit_mir

theorem wrap_control_wrong_shape :
    ¬ ∃ σ s : ℤ, (bp [(4, 0, 0), (2, 3, 1), (4, -2, -2)] = C σ * T s * pTile 1 2 ∨
                  bp [(4, 0, 0), (2, 3, 1), (4, -2, -2)] = C σ * T s * qTile 1 2) :=
  control_wrong_shape

example : True := trivial

#print axioms BAD.wit_rot
#print axioms BAD.control_wrong_shape

end Erdos634.Draft.BADPlacementWitWrap
