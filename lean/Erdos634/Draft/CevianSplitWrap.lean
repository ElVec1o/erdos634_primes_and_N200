import Erdos634.CevianSplit

namespace Erdos634.Draft.CevianSplitWrap

open Erdos634.CevianSplit

theorem cs_split_count (e f : ℤ) : f ^ 2 + (2 * f ^ 2 - e ^ 2) = 3 * f ^ 2 - e ^ 2 :=
  split_count e f

theorem cs_split_count_m (e f m : ℤ) :
    (f * m) ^ 2 + m ^ 2 * (2 * f ^ 2 - e ^ 2) = m ^ 2 * (3 * f ^ 2 - e ^ 2) :=
  split_count_m e f m

theorem cs_cevian_foot (e f m : ℤ) :
    e * m * (3 * f ^ 2 - e ^ 2) - e * f ^ 2 * m = e * m * (2 * f ^ 2 - e ^ 2) :=
  cevian_foot e f m

theorem cs_scaled_piece_sides (e f m : ℤ) :
    (f * m) * (e * f) = e * f ^ 2 * m
      ∧ (f * m) * (f ^ 2 - e ^ 2) = f * (f ^ 2 - e ^ 2) * m
      ∧ (f * m) * f ^ 2 = f ^ 3 * m :=
  scaled_piece_sides e f m

example : cs_split_count 1 2 = split_count 1 2 := rfl

#print axioms cs_scaled_piece_sides

end Erdos634.Draft.CevianSplitWrap
