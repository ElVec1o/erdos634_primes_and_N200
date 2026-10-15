import Erdos634.N1GapSubcases
namespace Erdos634.Draft.N1GapSubcasesWrap
open Erdos634.N1Gap Erdos634.N1GapSubcases
variable {e f a b c : ℕ}

theorem wrap_a_not_dvd_b (M : Member e f a b c) : ¬ (a ∣ b) :=
  a_not_dvd_b M

theorem wrap_a_pos (M : Member e f a b c) : 0 < a :=
  a_pos M

theorem wrap_prefix_all_a (M : Member e f a b c) {x y z s : ℕ}
    (hs : x * a + y * b + z * c = s) (hlt : s < b) : y = 0 ∧ z = 0 ∧ s = x * a :=
  prefix_all_a M hs hlt

theorem wrap_adm_iff (M : Member e f a b c) {x L : ℕ} (hL : L = a ∨ L = b ∨ L = c) :
    (x * a < b ∧ b < x * a + L) ↔
      (L = c ∧ x ≤ b / a) ∨ (L = b ∧ 1 ≤ x ∧ x ≤ b / a) ∨ (L = a ∧ x = b / a) :=
  adm_iff M hL

theorem wrap_card_adm (M : Member e f a b c) :
    ((Finset.range (b / a + 1) ×ˢ ({a, b, c} : Finset ℕ)).filter
      (fun p => p.1 * a < b ∧ b < p.1 * a + p.2)).card = 2 * (b / a) + 2 :=
  card_adm M

theorem wrap_member_witness : Member 2 5 10 21 25 := member_witness

example : True := trivial
#print axioms wrap_card_adm
end Erdos634.Draft.N1GapSubcasesWrap
