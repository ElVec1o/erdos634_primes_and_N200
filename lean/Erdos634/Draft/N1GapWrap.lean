import Erdos634.N1Gap
namespace Erdos634.Draft.N1GapWrap
open Erdos634.N1Gap Erdos634.ChordInterface
variable {e f a b c : ℕ}

theorem wrap_Member_a_lt_b (M : Member e f a b c) : a < b :=
  M.a_lt_b

theorem wrap_Member_b_lt_c (M : Member e f a b c) : b < c :=
  M.b_lt_c

theorem wrap_c_overrun (M : Member e f a b c) : c - b = e * e :=
  c_overrun M

theorem wrap_a_short_is_gap (M : Member e f a b c) (x y z : ℕ)
    (h : x * a + y * b + z * c = b - a) : False :=
  a_short_is_gap M x y z h

theorem wrap_b_exact_is_partner (M : Member e f a b c) (x y z : ℕ)
    (h : x * a + y * b + z * c = b) : x = 0 ∧ y = 1 ∧ z = 0 :=
  b_exact_is_partner M x y z h

theorem wrap_no_cheaper_repair (M : Member e f a b c) :
    (∀ x y z : ℕ, x * a + y * b + z * c = b → x = 0 ∧ y = 1 ∧ z = 0) ∧
    (∀ x y z : ℕ, ¬ (x * a + y * b + z * c = b - a)) ∧
    (c - b = e * e ∧ 0 < e * e) :=
  no_cheaper_repair M

example : True := trivial
#print axioms wrap_no_cheaper_repair
end Erdos634.Draft.N1GapWrap
