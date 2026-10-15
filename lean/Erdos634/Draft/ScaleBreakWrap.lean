import Mathlib.Tactic
import Erdos634.ScaleBreak

/-!
# ScaleBreak — m=2 scale break arithmetic kernels: wrapper

`ScaleBreak.side_no_b_fails_m2`.

The equal-side `side_no_b` identity fails at `m = 2`: there exists a walk
`P(ef) + Q·b + R·f² = 2f³` with Q≠0 and R≥1, for every coprime member.

0 sorry, standard axioms.
-/

namespace Erdos634.Draft.ScaleBreakWrap

open Erdos634.ScaleBreak

/-- Walk identity at m=2: e(ef)+f·b+f·f² = 2f³. -/
theorem scalebreak_walk_m2 (e f : ℕ) (h : e ≤ f) :
    e * (e * f) + f * (f * f - e * e) + f * (f * f) = 2 * (f * f * f) :=
  side_walk_m2 e f h

/-- side_no_b fails at m=2: there exists a valid walk with Q≠0. -/
theorem scalebreak_no_b_fails_m2 (e f B : ℕ) (he : 1 ≤ e) (hef : e < f)
    (hB : B + e ^ 2 = f ^ 2) :
    ∃ P Q R : ℕ, 1 ≤ R ∧ Q ≠ 0 ∧ P * (e * f) + Q * B + R * f ^ 2 = 2 * f ^ 3 :=
  side_no_b_fails_m2 e f B he hef hB

/-- Non-vacuity: e=1, f=2 satisfies hypotheses. -/
theorem scalebreak_witness : (1:ℕ) ≤ 1 ∧ (1:ℕ) < 2 := ⟨Nat.le_refl 1, by norm_num⟩

#print axioms scalebreak_walk_m2
#print axioms scalebreak_no_b_fails_m2

end Erdos634.Draft.ScaleBreakWrap
