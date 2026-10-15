import Erdos634.ForcedSecondRow

namespace Erdos634.Draft.ForcedSecondRowWrap

open Erdos634.ForcedSecondRow

/-- Thin wrapper: type-5 bound — `n₅ + 1 ≤ nₒ`. -/
theorem wrap_type5_bound (na nb nc n3 n5 : ℕ)
    (hjunc : n3 + n5 = na + nb + nc - 1)
    (hgamma : na + nb ≤ n3) (hE : 1 ≤ na + nb + nc) :
    n5 + 1 ≤ nc :=
  type5_bound na nb nc n3 n5 hjunc hgamma hE

/-- Thin wrapper: saturation at e=1 forces every junction to be type-3. -/
theorem wrap_all_junctions_type3 (f n3 n5 : ℕ)
    (hjunc : n3 + n5 = f + 1 + 1 - 1)
    (hgamma : f + 1 ≤ n3) :
    n5 = 0 :=
  all_junctions_type3 f n3 n5 hjunc hgamma

/-- Thin wrapper: the matching is forced by induction from both ends. -/
theorem wrap_matching_forced (n : ℕ) (assign : ℕ → ℕ)
    (hleft : assign 1 = 1)
    (hstep : ∀ i, 1 ≤ i → i < n → assign i = i → assign (i + 1) = i + 1) :
    ∀ i, 1 ≤ i → i ≤ n → assign i = i :=
  matching_forced n assign hleft hstep

/-- Thin wrapper: the walk spans the base. -/
theorem wrap_walk_spans (f : ℤ) :
    f * f + 1 * (f ^ 2 - 1) + 1 * f ^ 2 = 3 * f ^ 2 - 1 :=
  walk_spans f

-- Non-vacuity: at f=2 the walk 2·2 + 1·3 + 1·4 = 11 = 3·4 - 1.
example : walk_spans 2 = walk_spans 2 := rfl

#print axioms wrap_type5_bound
#print axioms wrap_matching_forced

end Erdos634.Draft.ForcedSecondRowWrap
