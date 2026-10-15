import Erdos634.GammaCount

namespace Erdos634.Draft.GammaCountWrap

open Erdos634.GammaCount

theorem gc_c_edge_exists (na nb nc : ℕ) (hE : 1 ≤ na + nb + nc)
    (htrap : na + nb ≤ na + nb + nc - 1) : 1 ≤ nc :=
  c_edge_exists na nb nc hE htrap

theorem gc_two_words (t : ℤ) (h012 : 0 ≤ t ∧ t ≤ 2) (hne2 : t ≠ 2) : t = 0 ∨ t = 1 :=
  two_words t h012 hne2

theorem gc_survivors (e f : ℤ) :
    (0 * (e * f) + e * (f ^ 2 - e ^ 2) + (2 * e) * f ^ 2 = e * (3 * f ^ 2 - e ^ 2))
      ∧ (f * (e * f) + e * (f ^ 2 - e ^ 2) + e * f ^ 2 = e * (3 * f ^ 2 - e ^ 2)) :=
  survivors e f

example : gc_two_words 1 ⟨by norm_num, by norm_num⟩ (by norm_num) = Or.inr rfl := rfl

#print axioms gc_survivors

end Erdos634.Draft.GammaCountWrap
