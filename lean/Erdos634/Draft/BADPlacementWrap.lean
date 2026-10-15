import Erdos634.BADPlacement

namespace Erdos634.Draft.BADPlacementWrap

open BAD
open LaurentPolynomial

-- Re-exports: single-tile boundary polynomial (layer L1)

theorem wrap_kk_period (i j : ℤ) : kk (i + 6) (j + 4) = kk i j :=
  kk_period i j

theorem wrap_ee_shift (i j m n : ℤ) : ee (i + m) (j + n) = ee i j * ee m n :=
  ee_shift i j m n

theorem wrap_ee_period (i j : ℤ) : ee (i + 6) (j + 4) = ee i j :=
  ee_period i j

theorem wrap_p_form (e f : ℤ) :
    C (f ^ 2) + C (f ^ 2 - e ^ 2) * T 2 + C (e * f) * (T 3 : L) = pTile e f :=
  p_form e f

example : True := trivial

#print axioms BAD.kk_period
#print axioms BAD.ee_period

end Erdos634.Draft.BADPlacementWrap
