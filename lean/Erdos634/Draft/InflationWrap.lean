import Erdos634.Inflation

namespace Erdos634.Draft.InflationWrap

open Erdos634.Inflation

theorem inf_sum_zero_or_three {w : List ℕ} (h : ∀ x ∈ w, isSide x) : w.sum = 0 ∨ 3 ≤ w.sum :=
  sum_zero_or_three h

theorem inf_middle_three (w : List ℕ) (h : ∀ x ∈ w, isSide x) (hs : w.sum = 3) : w = [3] :=
  middle_three w h hs

theorem inf_c_side_words : ([9, 9, 9] : List ℕ).sum = 27 ∧ ([9, 3, 3, 3, 9] : List ℕ).sum = 27 :=
  c_side_words

theorem inf_a_b_sides_rigid : ([3, 3, 3] : List ℕ).sum = 9 ∧ ([8, 8, 8] : List ℕ).sum = 24 :=
  a_b_sides_rigid

example : inf_c_side_words = c_side_words := rfl

#print axioms inf_sum_zero_or_three
#print axioms inf_c_side_words

end Erdos634.Draft.InflationWrap
