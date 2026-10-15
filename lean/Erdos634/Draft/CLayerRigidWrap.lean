import Erdos634.CLayerRigid

/-!
# C-layer rigidity: wrapper

Re-exports results of `CLayerRigid`:
- `offset_pos`: offset e²(3f²−e²) > 0
- `offset_lt_two`: offset < 2f⁴
- `offset_ne_one`: offset ≠ f⁴ when e, f coprime
- `left_gap_not_tiles`: left gap cannot tile
- `mixed_gap_not_tiles`: mixed gap cannot tile
- `reverse_gap_not_tiles`: reverse gap cannot tile
- `c_layer_rigid`: C-layer is rigid (all three gap types excluded)

No `sorry`; standard axioms only.
-/

namespace Erdos634.Draft.CLayerRigidWrap

open Erdos634.CLayerRigid

theorem clr_offset_pos (e f : ℤ) (he : 1 ≤ e) (hef : e < f) :
    0 < e ^ 2 * (3 * f ^ 2 - e ^ 2) :=
  offset_pos e f he hef

theorem clr_offset_lt_two (e f : ℤ) (he : 1 ≤ e) (hef : e < f) :
    e ^ 2 * (3 * f ^ 2 - e ^ 2) < 2 * f ^ 4 :=
  offset_lt_two e f he hef

theorem clr_left_gap_not_tiles (e f n : ℤ) (he : 1 ≤ e) (hef : e < f) (hcop : IsCoprime e f)
    (hn : 0 ≤ n) : n * f ^ 4 ≠ f ^ 4 - e ^ 2 * (3 * f ^ 2 - e ^ 2) :=
  left_gap_not_tiles e f n he hef hcop hn

theorem clr_c_layer_rigid (e f : ℤ) (he : 1 ≤ e) (hef : e < f) (hcop : IsCoprime e f) :
    (∀ n : ℤ, 0 ≤ n → n * f ^ 4 ≠ f ^ 4 - e ^ 2 * (3 * f ^ 2 - e ^ 2))
      ∧ (∀ n : ℤ, 0 ≤ n → n * f ^ 4 ≠ 2 * f ^ 4 - e ^ 2 * (3 * f ^ 2 - e ^ 2))
      ∧ (∀ n : ℤ, 0 ≤ n → n * f ^ 4 ≠ e ^ 2 * (3 * f ^ 2 - e ^ 2)) :=
  c_layer_rigid e f he hef hcop

-- Non-vacuity: offset_pos at e=1, f=2
example : (0:ℤ) < 1 ^ 2 * (3 * 2 ^ 2 - 1 ^ 2) := clr_offset_pos 1 2 (by norm_num) (by norm_num)

#print axioms clr_c_layer_rigid
#print axioms clr_offset_pos

end Erdos634.Draft.CLayerRigidWrap
