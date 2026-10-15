import Erdos634.N1GapMastGap
namespace Erdos634.Draft.N1GapMastGapWrap
open Erdos634.N1Gap Erdos634.N1GapSubcases Erdos634.N1GapMastGap
variable {e f a b c : ℕ}

theorem wrap_two_a_lt_b (M : Member e f a b c) : 2 * a < b :=
  two_a_lt_b M

theorem wrap_crossing_index_ge_two (M : Member e f a b c) : 2 ≤ b / a :=
  crossing_index_ge_two M

theorem wrap_card_adm_ge_six (M : Member e f a b c) :
    6 ≤ ((Finset.range (b / a + 1) ×ˢ ({a, b, c} : Finset ℕ)).filter
      (fun p => p.1 * a < b ∧ b < p.1 * a + p.2)).card :=
  card_adm_ge_six M

theorem wrap_mast_vacuous_at_crossing (M : Member e f a b c) :
    ¬ (2 * ((b / a : ℕ) + 1 : ℤ) * ((e : ℤ) * (f : ℤ)) * (f : ℤ)
        < (e : ℤ) * (3 * (f : ℤ) ^ 2 - (e : ℤ) ^ 2)) :=
  mast_vacuous_at_crossing M

theorem wrap_b_range_homogeneous (M : Member e f a b c) :
    ∀ x, 1 ≤ x → x ≤ b / a →
      (0 < x * a ∧ x * a < b) ∧ (∀ L', L' = b ∨ L' = c → x * a < L') :=
  b_range_homogeneous M

theorem wrap_c_range_type_changes :
    (0 * 10 + 2 * 2 : ℕ) < 21 ∧ 21 < (2 * 10 + 2 * 2 : ℕ) :=
  c_range_type_changes

example : True := trivial
#print axioms wrap_mast_vacuous_at_crossing
end Erdos634.Draft.N1GapMastGapWrap
