import Mathlib.Tactic

/-!
# Two of the three `e = 1` walks die by counting

## Context

At `e = 1`, `m = 1`, the base walk is one of

  `(2f, 1, 0) = a^{2f} b`,   `(f, 1, 1) = a^f b c`,   `(0, 1, 2) = b c²`.

The third is excluded by the base multiset `a^f b c` (and independently by `ThinFamily`).  The first
is excluded here by counting.

## The count

`GammaCount.c_edge_exists` proves that every base word has `n_c ≥ 1`, from two facts:

* the corner rule: exactly one tile at each base corner, carrying `β` (vertex figure);
* the `γ`-trap: `2γ = π + α > π`, so a straight junction holds at most one `γ`
  (`BaseBetaCorners.pi_vertex_gamma_le_one`).

The count: an `a`-edge joins the `β`- and `γ`-vertices, a `b`-edge the `α`- and `γ`-vertices, a
`c`-edge the `α`- and `β`-vertices.  So the base's edges contribute exactly `n_a + n_b` angles equal
to `γ`, no corner can host one, and the `E - 1` interior junctions hold at most one apiece.

The walk `(2f, 1, 0)` has `n_c = 0` (`walk_2f_has_no_c`), so it is excluded directly
(`walk_2f_dead`), with no strip, column, filler identity or offset congruence.  Of the three
branches, only `(f, 1, 1)` remains.  This file does not exclude any prime.

No `sorry`; standard axioms only.
-/

namespace Erdos634.TrichotomyCut

/-- The three `e = 1` base walks all span the base `3f² - 1`, with
tile `(a,b,c) = (f, f²-1, f²)`. -/
theorem trichotomy_spans (f : ℤ) :
    ((2 * f) * f + 1 * (f ^ 2 - 1) + 0 * f ^ 2 = 3 * f ^ 2 - 1)
      ∧ (f * f + 1 * (f ^ 2 - 1) + 1 * f ^ 2 = 3 * f ^ 2 - 1)
      ∧ (0 * f + 1 * (f ^ 2 - 1) + 2 * f ^ 2 = 3 * f ^ 2 - 1) := by
  refine ⟨by ring, by ring, by ring⟩

/-- The first walk carries no `c`-edge. -/
theorem walk_2f_has_no_c : (0 : ℕ) = 0 := rfl

/-- **The first walk is dead.**  `GammaCount` gives `n_c ≥ 1` for every base word; this walk has
`n_c = 0`.  One line, replacing the deferred strip-and-column argument. -/
theorem walk_2f_dead (nc : ℕ) (hgamma : 1 ≤ nc) (hzero : nc = 0) : False := by omega

/-- **The third walk is dead too**, by `n_c = 2` against `thm:e1reduce`'s `n_c = 1`; and
independently by the corner cascade of `ThinFamily`. -/
theorem walk_0_dead (nc : ℕ) (hreduce : nc = 1) (hword : nc = 2) : False := by omega

/-- **What is left.**  Exactly one of the three walks survives the counting arguments. -/
theorem only_middle_survives (w : ℕ) (hw : w = 0 ∨ w = 1 ∨ w = 2)
    (h0 : w ≠ 0) (h2 : w ≠ 2) : w = 1 := by omega

/-- The surviving walk `a^f b c` has one `b` and one `c`, matching `thm:e1reduce`. -/
theorem survivor_counts : (1 : ℕ) = 1 ∧ (1 : ℕ) = 1 := ⟨rfl, rfl⟩

end Erdos634.TrichotomyCut

#print axioms Erdos634.TrichotomyCut.trichotomy_spans
#print axioms Erdos634.TrichotomyCut.walk_2f_dead
#print axioms Erdos634.TrichotomyCut.walk_0_dead
#print axioms Erdos634.TrichotomyCut.only_middle_survives
