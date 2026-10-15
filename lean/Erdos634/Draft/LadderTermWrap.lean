import Erdos634.OrderForcing

/-!
# Ladder termination arithmetic kernel

A ladder terminates only where both of its staggered covers end
simultaneously, i.e. the two cover endpoints coincide. The arithmetic content is:

- The semigroup `S = ⟨f, f²−1, f²⟩` has NO two consecutive members below `f²`: if both `m`
  and `m+1` lie in `S`, then `m+1 ≥ f²`. (`consecutive_gap`)
- Consequence: the ladder's termination parameter `T = b + m` satisfies `T ≥ b + f² = 2f²−1`,
  strictly exceeding `2b = 2(f²−1)` and requiring at least three strips of clearance.
- The target is exactly `f` strips tall: `f³ = f·f²`. (`strips_tall`)

The ladder itself (a `CongruentDissection` with an interior "T-vertex" column and staggered covers) has no
definition in this file; only the arithmetic is formalized.

No sorry; axioms [propext, Classical.choice, Quot.sound] (from consecutive_gap's interval_cases).
-/

namespace Erdos634.Draft.LadderTermWrap

open Erdos634.OrderForcing

/-- If both `m` and `m+1` lie in `⟨f, f²−1, f²⟩`, then `m+1 ≥ f²`. -/
theorem ladder_termination_bound {f m x1 y1 z1 x2 y2 z2 : ℕ} (hf : 3 ≤ f)
    (h1 : x1 * f + y1 * (f * f - 1) + z1 * (f * f) = m)
    (h2 : x2 * f + y2 * (f * f - 1) + z2 * (f * f) = m + 1) :
    f * f ≤ m + 1 :=
  consecutive_gap hf h1 h2

/-- The termination parameter `T ≥ b + c = 2f² − 1` exceeds `2b = 2(f²−1)`. -/
theorem ladder_needs_three_strips (f : ℕ) :
    2 * (f * f - 1) < (f * f - 1) + f * f ∨ f = 0 :=
  ladder_three_strips f

/-- The target is exactly `f` strips tall: `f³ = f · f²`. -/
theorem target_height_f_strips (f : ℕ) : f ^ 3 = f * f ^ 2 :=
  strips_tall f

/-- Non-vacuity: at f=3, there exist m,x1,y1,z1,x2,y2,z2 satisfying the hypotheses. -/
theorem termination_witness :
    ∃ m x1 y1 z1 x2 y2 z2 : ℕ,
      x1 * 3 + y1 * (3 * 3 - 1) + z1 * (3 * 3) = m ∧
      x2 * 3 + y2 * (3 * 3 - 1) + z2 * (3 * 3) = m + 1 := by
  exact ⟨8, 0, 1, 0, 0, 0, 1, by norm_num, by norm_num⟩

#print axioms ladder_termination_bound
#print axioms ladder_needs_three_strips
#print axioms target_height_f_strips

end Erdos634.Draft.LadderTermWrap
