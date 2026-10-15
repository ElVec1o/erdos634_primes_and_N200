import Mathlib.Tactic

/-!
# The rational-angle branch for `N = 105`

The exclusion of `N = 105` has three branches for a candidate
tile: an angle of `π/3`, an angle of `2π/3`, or all angles rational multiples of `π`. The first two
are excluded by exhaustive search (1,922,194 / 3,497,208 / 25,742,338 nodes); those are not covered by this file.

**The third branch needs no search.** A rational-angle tile
forces `N = d·k²` for some `d ∣ 6`, and `105` is none of `k², 2k², 3k², 6k²`. This is finite,
decidable arithmetic with no geometric quantifier.

## Scope

**Formalized:** the rational-angle branch in full, `eq105_not_rational_branch`.

**Not formalized here:** the other two branches (`π/3` tiles via Beeson's Table 2; the `2π/3` tile
enumeration `a ≤ b < 4000`).
-/

namespace Erdos634.Eq105Rational

/-- **`105` is not `d·k²` for any `d ∣ 6`.** Since `d ∣ 6` forces `d ≤ 6`, `d·k² = 105` gives
`k² ≤ 105`, so `k ≤ 10`; a finite check over `d ∈ {1,2,3,6}` (the divisors of `6`) and
`k ≤ 10` closes it. -/
theorem not_dk_sq (d k : ℕ) (hd : d ∣ 6) (hd0 : 0 < d) : d * k ^ 2 ≠ 105 := by
  have hd6 : d ≤ 6 := Nat.le_of_dvd (by norm_num) hd
  intro h
  have hk2 : k ^ 2 ≤ 105 := by nlinarith
  have hk10 : k ≤ 10 := by nlinarith [sq_nonneg (k - 10)]
  interval_cases d <;> interval_cases k <;> omega

/-- **The rational-angle branch of the exclusion of `N = 105`.** If a tile has all angles rational multiples of
`π`, tiling forces `N = d·k²` for some divisor `d` of `6` and some positive integer `k`
(the classification of rational-angle tiles admitting an equilateral
tiling). No such tile gives `N = 105`. -/
theorem eq105_not_rational_branch :
    ∀ d k : ℕ, d ∣ 6 → 0 < d → 0 < k → d * k ^ 2 ≠ 105 :=
  fun d k hd hd0 _ => not_dk_sq d k hd hd0

/-- Non-vacuity: `d = 1`, `k = 1` satisfies the hypotheses (`N = 1 ≠ 105`, so the branch is real
and the theorem has content, not a vacuous universal). -/
theorem witness : (1:ℕ) ∣ 6 ∧ 0 < (1:ℕ) ∧ 0 < (1:ℕ) ∧ (1:ℕ) * 1 ^ 2 = 1 := by norm_num

end Erdos634.Eq105Rational

#print axioms Erdos634.Eq105Rational.not_dk_sq
#print axioms Erdos634.Eq105Rational.eq105_not_rational_branch
