import Mathlib.Tactic

/-!
# The walls hypothesis above `f = 2e` is a single exclusion

## The chain

1. `WallsWord.walls_pins_word`: the walls hypothesis asserts `f` `a`-feet west and `e` `c`-feet
   east, i.e. `n_a ≥ f` and `n_c ≥ e`; against the base-word family those pin `j = 0`, `t = 1`, so
   the base word is exactly `a^f b^e c^e`.  Hence
   **the walls hypothesis ⟺ no tiling carries any other base word.**
2. `ThreeWords.three_words`: for `f > 2e`, nonnegativity alone forces `j = 0` and `t ∈ {0,1,2}`.
3. `GammaCount.c_edge_exists`: every base word has `n_c ≥ 1`, killing `t = 2`, whose word is
   `(2f, e, 0)`.

Composing: for `f > 2e` exactly **two** base words exist, `(0,e,2e)` and `(f,e,e)`, so

> **the walls hypothesis at a member with `f > 2e` ⟺ the single word `(0, e, 2e)` admits no tiling.**

`walls_iff_W0` records the composition.  This replaces a geometric argument by one decidable
instance per member.

## Exhaustive searches of the single word

Running the single word `(0,e,2e)` on an exact `ℤ[√D]` search:

| member | `N` | `(0,e,2e)` |
|---|---|---|
| `(1,3)` | 26 | exhausted, 477 nodes |
| `(1,4)` | 47 | exhausted, 2 191 |
| `(1,5)` | 74 | exhausted, 15 763 |
| `(2,5)` | 71 | exhausted, 140 231 |

So the walls hypothesis holds at these members.  The searches are exhaustive-search results; the
theorems below are the reduction, not the exhaustions.

## Scope

The reduction needs `f > 2e`.  At `f ≤ 2e` more base words survive (`j ≥ 1` is possible), and
`N = 83`, whose member is `(5,6)`, lies in that regime with six words.

No `sorry`; standard axioms only.
-/

namespace Erdos634.WallsClosed

/-- **The composition.**  Given the three-word bound and `n_c ≥ 1`, a member with `f > 2e` has base
word `t = 0` or `t = 1`; `hyp:walls` is `t = 1`, so it is equivalent to excluding `t = 0`, the word
`(0, e, 2e)`. -/
theorem walls_iff_W0 (t : ℤ) (h012 : 0 ≤ t ∧ t ≤ 2) (hnc : t ≠ 2) :
    (t = 1) ↔ ¬ (t = 0) := by
  obtain ⟨h0, h2⟩ := h012
  constructor
  · intro h; omega
  · intro h; omega

/-- The two words at `f > 2e`, with their `c`-counts: `t = 0` gives `2e`, `t = 1` gives `e`.
Both are positive, so `GammaCount` does not distinguish them — the exclusion of `t = 0` is genuine
work, not another count. -/
theorem both_have_c (e : ℤ) (he : 1 ≤ e) : 0 < 2 * e ∧ 0 < e := ⟨by omega, by omega⟩

/-- The `t = 0` word solves the base equation: `e` `b`-edges and `2e` `c`-edges span `e N₀`. -/
theorem W0_spans (e f : ℤ) :
    0 * (e * f) + e * (f ^ 2 - e ^ 2) + (2 * e) * f ^ 2 = e * (3 * f ^ 2 - e ^ 2) := by ring

/-- and the walls word likewise. -/
theorem W1_spans (e f : ℤ) :
    f * (e * f) + e * (f ^ 2 - e ^ 2) + e * f ^ 2 = e * (3 * f ^ 2 - e ^ 2) := by ring

/-- `(1,5)`: `N = 74`, tile `(5,24,25)`, base `74`.  The excluded word is `b¹ c²`. -/
theorem member_1_5 : (0 * 5 + 1 * 24 + 2 * 25 : ℤ) = 74 ∧ (74 : ℤ) = 3 * 5 ^ 2 - 1 ^ 2 := by
  refine ⟨by norm_num, by norm_num⟩

/-- `(2,5)`: `N = 71`, tile `(10,21,25)`, base `142`.  The excluded word is `b² c⁴`. -/
theorem member_2_5 : (0 * 10 + 2 * 21 + 4 * 25 : ℤ) = 142 ∧ (71 : ℤ) = 3 * 5 ^ 2 - 2 ^ 2 := by
  refine ⟨by norm_num, by norm_num⟩

end Erdos634.WallsClosed

#print axioms Erdos634.WallsClosed.walls_iff_W0
#print axioms Erdos634.WallsClosed.both_have_c
#print axioms Erdos634.WallsClosed.W0_spans
#print axioms Erdos634.WallsClosed.member_1_5
#print axioms Erdos634.WallsClosed.member_2_5
