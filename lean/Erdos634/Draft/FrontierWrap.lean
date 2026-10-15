import Erdos634.Frontier

namespace Erdos634.Draft.FrontierWrap

open Erdos634.Frontier

/-- Thin wrapper: a south-straddle gap is not in the semi-group. -/
theorem wrap_gap_south_straddle {f t n : ℕ} (hf : 3 ≤ f) (ht1 : 1 ≤ t) (htf : t < f)
    (hn : n + f + t = f * f) :
    ¬ inSemi 1 f n :=
  gap_south_straddle hf ht1 htf hn

/-- Thin wrapper: east-cover gap. -/
theorem wrap_gap_east_cover {f n : ℕ} (hf : 3 ≤ f) (hn : n + 1 + f = f * f) :
    ¬ inSemi 1 f n :=
  gap_east_cover hf hn

/-- Thin wrapper: arithmetic reduction for base columns. -/
theorem wrap_base_column_reduction (e f k x z : ℤ) :
    x * (e * f) + (e + k * f) * (f * f - e * e) + z * (f * f) - e * (3 * f * f - e * e)
      = f * (x * e + z * f - (2 * e * f - k * (f * f - e * e))) :=
  base_column_reduction e f k x z

/-- Thin wrapper: one-column-per-k multiplicity bound. -/
theorem wrap_one_column_per_k {e f k q : ℕ} (he : 0 < e) (hef : e < f) (hk : 1 ≤ k)
    (hq : q * f ≤ k * e) (hq' : k * e < (q + 1) * f) :
    e * (1 + q) ≤ k * f :=
  one_column_per_k he hef hk hq hq'

-- Non-vacuity: at f=3, e=1 the semi-group contains 3 = 1·a.
example : inSemi 1 3 3 := ⟨1, 0, 0, by simp [inSemi, sideA, sideB, sideC]⟩

#print axioms wrap_gap_south_straddle
#print axioms wrap_one_column_per_k

end Erdos634.Draft.FrontierWrap
