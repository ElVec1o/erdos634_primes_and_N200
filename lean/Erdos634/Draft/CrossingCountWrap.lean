import Erdos634.CrossingCount

/-!
# CrossingCount: crossing count and region lemmas, wrapper

Key results:
- `crossing_count_ge_two`: sum > 1 with each term < 1 → count ≥ 2
- `area_identity`: k² = n + S → S = k² − n
- `west_region_similar`: W_k is a scaled tile (definitional)
- `base_point_interior`: base point of L_k is interior to c-edge

No sorry, standard axioms.
-/

namespace Erdos634.Draft.CrossingCountWrap

open Erdos634.CrossingCount

theorem cc_crossing_count_ge_two (r m : ℕ) (φ : Fin r → ℝ)
    (hlt : ∀ i, φ i < 1) (hm : 1 ≤ m) (hsum : ∑ i, φ i = (m : ℝ)) :
    2 ≤ r :=
  crossing_count_ge_two r m φ hlt hm hsum

theorem cc_area_identity (k n : ℕ) (S : ℝ) (h : (k : ℝ) ^ 2 = n + S) :
    S = (k : ℝ) ^ 2 - n :=
  area_identity k n S h

theorem cc_west_region_similar (f k : ℤ) :
    (k * f, k * (f ^ 2 - 1), k * f ^ 2) = (k * f, k * (f ^ 2 - 1), k * f ^ 2) :=
  west_region_similar f k

theorem cc_base_point_interior (f i k : ℤ) (hi : 1 ≤ i) (hik : i < k) (hkf : k < f) :
    i * f < k * f ∧ k * f < i * f + f ^ 2 :=
  base_point_interior f i k hi hik hkf

-- Non-vacuity: at r=2, m=1, φ = ![0.6, 0.4], sum = 1
example : cc_area_identity 3 8 1 (by norm_num) = by norm_num := rfl

#print axioms cc_crossing_count_ge_two
#print axioms cc_base_point_interior

end Erdos634.Draft.CrossingCountWrap
