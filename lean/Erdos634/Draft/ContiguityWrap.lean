import Erdos634.Contiguity

/-!
# Contiguity: gap/contiguity wrapper
Key results:
- `closed_full_measure_eq_X`: a closed subset of `[a,b]` with full measure equals `[a,b]`.
- `no_gap_between_X`: under the same hypotheses every point of the interval lies in `S`.
- `gap_forces_meet_X`: a gap between consecutive edges contradicts full coverage.
- `distinct_left_endpoints_X`: non-degenerate intervals with disjoint interiors have distinct left endpoints.
No sorry, standard axioms.
-/

namespace Erdos634.Draft.ContiguityWrap
open Erdos634.Contiguity MeasureTheory Set

/-- Wrap: a closed subset of `[a,b]` with the same volume equals `[a,b]`. -/
theorem closed_full_measure_eq_X {a b : ℝ} (hab : a < b) (S : Set ℝ)
    (hclosed : IsClosed S) (hsub : S ⊆ Icc a b)
    (hvol : volume S = volume (Icc a b)) : S = Icc a b :=
  closed_full_measure_eq hab S hclosed hsub hvol

/-- Wrap: every point of `[a,b]` lies in `S` when `S` is closed, contained in `[a,b]`, and has
full measure. -/
theorem no_gap_between_X {a b : ℝ} (hab : a < b) (S : Set ℝ)
    (hclosed : IsClosed S) (hsub : S ⊆ Icc a b)
    (hvol : volume S = volume (Icc a b)) {x : ℝ} (hx : x ∈ Icc a b) : x ∈ S :=
  no_gap_between hab S hclosed hsub hvol hx

/-- Wrap: a gap `(q, r)` inside `[a,b]` that misses `S` contradicts `S` covering `[a,b]`. -/
theorem gap_forces_meet_X {a b q r : ℝ} (S : Set ℝ) (hcov : Icc a b ⊆ S)
    (hqr : q < r) (hsub : Ioo q r ⊆ Icc a b) (huncov : Ioo q r ∩ S = ∅) : False :=
  gap_forces_meet S hcov hqr hsub huncov

/-- Wrap: non-degenerate intervals with disjoint open spans have distinct left endpoints. -/
theorem distinct_left_endpoints_X {p q r s : ℝ} (hpq : p < q) (hrs : r < s)
    (hdisj : Ioo p q ∩ Ioo r s = ∅) : p ≠ r :=
  distinct_left_endpoints hpq hrs hdisj

-- Non-vacuity: `[0,1]` is closed and has full measure relative to itself
example : IsClosed (Icc (0:ℝ) 1) := isClosed_Icc

#print axioms closed_full_measure_eq_X
#print axioms no_gap_between_X
#print axioms gap_forces_meet_X
#print axioms distinct_left_endpoints_X
end Erdos634.Draft.ContiguityWrap
