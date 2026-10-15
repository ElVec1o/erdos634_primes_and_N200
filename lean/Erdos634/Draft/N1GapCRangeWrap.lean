import Erdos634.N1GapCRange
namespace Erdos634.Draft.N1GapCRangeWrap
open Erdos634.N1Gap Erdos634.N1GapSubcases Erdos634.N1GapCRange
variable {e f a b c : ℕ}

theorem wrap_f_ge_three (M : Member e f a b c) : 3 ≤ f :=
  f_ge_three M

theorem wrap_e_sq_lt_a (M : Member e f a b c) : e * e < a :=
  e_sq_lt_a M

theorem wrap_overhang_ne_b (M : Member e f a b c) (x : ℕ) : x * a + e * e ≠ b :=
  overhang_ne_b M x

theorem wrap_mod_ne_e_sq (M : Member e f a b c) : b % a ≠ e * e :=
  mod_ne_e_sq M

theorem wrap_c_range_dichotomy (M : Member e f a b c) :
    (b % a < e * e ∧ ∀ x, x ≤ b / a → (b < x * a + e * e ↔ x = b / a)) ∨
    (e * e < b % a ∧ ∀ x, x ≤ b / a → x * a + e * e < b) :=
  c_range_dichotomy M

theorem wrap_two_vertices_iff (M : Member e f a b c) :
    ((b / a) * a < b ∧ b < (b / a) * a + c) ∧ (2 * b < (b / a) * a + c ↔ b % a < e * e) :=
  two_vertices_iff M

example : True := trivial
#print axioms wrap_c_range_dichotomy
end Erdos634.Draft.N1GapCRangeWrap
