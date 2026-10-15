import Erdos634.InvariantProduct

/-!
# InvariantProduct — F1 invariant product algebra: wrapper

`InvariantProduct.*` provides the algebraic identities for the F1-invariant product argument.

No sorry; standard axioms.
-/

namespace Erdos634.Draft.InvariantProductWrap

open Erdos634.InvariantProduct

theorem invprod_F1_num (a b c : ℤ) (hc : c ^ 2 = a ^ 2 + a * b + b ^ 2) :
    (2 * a + b - c) * (2 * a + b + c) = 3 * a * (a + b) :=
  F1_num a b c hc

theorem invprod_XY_eq (a b c : ℤ) (hc : c ^ 2 = a ^ 2 + a * b + b ^ 2) :
    (c + a - b) * (c + b - a) = 3 * (a * b) :=
  XY_eq a b c hc

theorem invprod_F1_Ma (a b c k Ma : ℤ) (hc : c ^ 2 = a ^ 2 + a * b + b ^ 2) (ha : a ≠ 0)
    (hMa : Ma * (c + a - b) = k * (2 * a + b - c)) : Ma * b = k * (c - a) :=
  F1_Ma a b c k Ma hc ha hMa

theorem invprod_F1_Mb (a b c k Mb : ℤ) (hc : c ^ 2 = a ^ 2 + a * b + b ^ 2) (ha : a ≠ 0)
    (hMb : Mb * (c + b - a) = k * (2 * a + b + c)) : Mb * b = k * (c + a) :=
  F1_Mb a b c k Mb hc ha hMb

theorem invprod_F1_product (a b c k N Ma Mb : ℤ) (hc : c ^ 2 = a ^ 2 + a * b + b ^ 2)
    (ha : a ≠ 0) (hb : b ≠ 0)
    (hN : N * b = k ^ 2 * (a + b))
    (hMa : Ma * (c + a - b) = k * (2 * a + b - c))
    (hMb : Mb * (c + b - a) = k * (2 * a + b + c)) :
    Ma * Mb = N :=
  F1_product a b c k N Ma Mb hc ha hb hN hMa hMb

theorem invprod_disc_not_square (N q : ℤ) (hN : 6 < N) :
    N ^ 2 + 14 * N + 1 ≠ q ^ 2 :=
  disc_not_square N q hN

theorem invprod_tile_similar_not_prime (N Ma : ℤ) (hN : N = Ma ^ 2) : ¬ Prime N :=
  tile_similar_not_prime N Ma hN

/-- Non-vacuity: (a=1,b=1,c=1): 1²=1+1+1 is false, but (a=1,b=2,c=√7) doesn't work nicely.
    Use (a=3,b=5,c=7): 7²=9+15+25=49. ✓ -/
theorem invprod_witness : (7:ℤ) ^ 2 = 3 ^ 2 + 3 * 5 + 5 ^ 2 := by norm_num

#print axioms invprod_F1_num
#print axioms invprod_F1_product
#print axioms invprod_disc_not_square

end Erdos634.Draft.InvariantProductWrap
