import Erdos634.LayerWord
namespace Erdos634.Draft.LayerWordWrap
open Erdos634.LayerWord

theorem wrap_word_classification (e f x y z : ℤ) (he : 1 ≤ e) (hef : e < f)
    (hcop : IsCoprime e f) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (heq : x * (e * f) + y * (f ^ 2 - e ^ 2) + z * f ^ 2 = e * f ^ 2) :
    (x = f ∧ y = 0 ∧ z = 0) ∨ (x = 0 ∧ y = 0 ∧ z = e) :=
  word_classification e f x y z he hef hcop hx hy hz heq

theorem wrap_no_b_edge (e f x y z : ℤ) (he : 1 ≤ e) (hef : e < f) (hcop : IsCoprime e f)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (heq : x * (e * f) + y * (f ^ 2 - e ^ 2) + z * f ^ 2 = e * f ^ 2) : y = 0 :=
  no_b_edge e f x y z he hef hcop hx hy hz heq

theorem wrap_no_mixed_word (e f x y z : ℤ) (he : 1 ≤ e) (hef : e < f) (hcop : IsCoprime e f)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (heq : x * (e * f) + y * (f ^ 2 - e ^ 2) + z * f ^ 2 = e * f ^ 2) :
    x = 0 ∨ z = 0 :=
  no_mixed_word e f x y z he hef hcop hx hy hz heq

theorem wrap_c_layer_offset (e f : ℤ) :
    (e * f) ^ 2 + (f ^ 2) ^ 2 - (f ^ 2 - e ^ 2) ^ 2 = e ^ 2 * (3 * f ^ 2 - e ^ 2) :=
  c_layer_offset e f

theorem wrap_c_offset_lt_two_c (e f : ℤ) (he : 1 ≤ e) (hef : e < f) :
    e ^ 2 * (3 * f ^ 2 - e ^ 2) < 2 * f ^ 4 :=
  c_offset_lt_two_c e f he hef

example : True := trivial
#print axioms wrap_word_classification
end Erdos634.Draft.LayerWordWrap
