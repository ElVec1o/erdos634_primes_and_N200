import Erdos634.Rationality

/-!
# Rationality — tile-angle rationality: wrapper

`Rationality.*` provides the algebraic identities showing that from the flux invariant,
both side ratios are rational.

Standard axioms, no `sorry`.
-/

namespace Erdos634.Draft.RationalityWrap

open Erdos634.Rationality

theorem rat_prod_eq {R : Type*} [CommRing R] (a b c P : R)
    (hc : c ^ 2 = a ^ 2 + a * b + b ^ 2) :
    (P * (c - a - b)) * (P * (c + a + b)) = -(P ^ 2 * (a * b)) :=
  prod_eq a b c P hc

theorem rat_sum_eq {R : Type*} [CommRing R] (a b c P : R)
    (hc : c ^ 2 = a ^ 2 + a * b + b ^ 2) :
    P ^ 2 * (b * (a + 2 * b)) + (P * (c - a - b)) * (P * (c + a + b)) = 2 * (P ^ 2 * b ^ 2) :=
  sum_eq a b c P hc

theorem rat_ratios_rational (a b c P : ℝ) (hc : c ^ 2 = a ^ 2 + a * b + b ^ 2)
    (hb : b ≠ 0) (hP : P ≠ 0) (hab : a + b ≠ 0) :
    a / b = -(2 : ℝ) * ((P * (c - a - b)) * (P * (c + a + b))) /
              (P ^ 2 * (b * (a + 2 * b)) + (P * (c - a - b)) * (P * (c + a + b)))
    ∧ c / (a + b) = ((P * (c - a - b)) + (P * (c + a + b))) /
              ((P * (c + a + b)) - (P * (c - a - b))) :=
  ratios_rational a b c P hc hb hP hab

theorem rat_tile_rational (a b c P : ℝ) (hc : c ^ 2 = a ^ 2 + a * b + b ^ 2)
    (hb : b ≠ 0) (hP : P ≠ 0) (hab : a + b ≠ 0)
    (nN nA nB : ℤ)
    (hN : (nN : ℝ) = P ^ 2 * (b * (a + 2 * b)))
    (hA : (nA : ℝ) = P * (c - a - b))
    (hB : (nB : ℝ) = P * (c + a + b)) :
    ∃ q r : ℚ, a = (q : ℝ) * b ∧ c = (r : ℝ) * b :=
  tile_rational a b c P hc hb hP hab nN nA nB hN hA hB

/-- Non-vacuity: (a=1,b=1,c=1) would need 1=1+1+1=3, false.
    Use (a=3,b=5,c=7): 7²=9+15+25=49. ✓ -/
theorem rat_witness : (7:ℝ) ^ 2 = 3 ^ 2 + 3 * 5 + 5 ^ 2 := by norm_num

#print axioms rat_prod_eq
#print axioms rat_ratios_rational
#print axioms rat_tile_rational

end Erdos634.Draft.RationalityWrap
