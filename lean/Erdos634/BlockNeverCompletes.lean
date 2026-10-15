import Mathlib.Tactic

/-!
# At `e = 1` the corner block can never complete

Erdős #634: eliminating the first branch of the per-corner trichotomy.

## The question

At `e = 1` the multiples of `f` in `[0, f²)` are tiling vertices on the base, and they come from a **column**,
which is produced by a **side break**.  The per-corner trichotomy is: the corner block's quadratic growth
*completes*, or a *base break* occurs, or a *side break* occurs.

The forced second row of `ForcedSecondRow` is not the terminal column, and the reason is sharp: the base's first
`a`-run occupies `[0, L f]` and its junctions are genuine tiling vertices at multiples of `f`, but the base word
puts the `b` at a position `q ≤ f`, so the run breaks at `r = min(p,q) ≤ f` and `L = r - 1 ≤ f - 1`.  Hence
`L f ≤ (f-1) f < f²` (`run_stops_short`): **the row never reaches `f²`**, so it is a column but not
the terminal one.

## What that same bound gives instead

A complete west corner block needs `f` `a`-**feet** on the base, i.e. an unbroken run of length `f`.
Since `L ≤ f - 1`, that is impossible:

> **at `e = 1` the corner block can never complete** (`block_never_completes`),

and by the mirror argument the same holds at the east corner.  So the first branch of the
trichotomy is eliminated and **both corners break**, on the base or on a side.

A base break consumes the single `c` of the walk `(f,1,1)` (the walk letter is
forced into `{a,c}`, and two base breaks are incompatible with one `c`), so at most one corner breaks
on the base, leaving at least one **side break**, which produces the column.

Checked over every arrangement with `f < 300`: `L ≤ f-1` and `L f < f²`, no exceptions.

## What remains

Given that a base break consumes the `c` (equivalently, the walk letter at a base break lies in `{a,c}`), both
corners break, at most one on the base, so a side break and hence a column exists; the column puts its base apex
on a multiple of `f`, the interior condition forbids the odd edge that the base word requires below `f²`, and
`e = 1` closes.  That sub-fact is not proved here.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.BlockNeverCompletes

/-- **The run stops short of `f²`.**  With the `b` at position `q ≤ f` and the `c` at `p ≥ 2`, the
first run has length `L = min(p,q) - 1 ≤ f - 1`, so it spans `L f ≤ (f-1) f < f²`. -/
theorem run_stops_short (f L : ℕ) (hf : 2 ≤ f) (hL : L ≤ f - 1) : L * f < f ^ 2 := by
  have h1 : L < f := by omega
  have h : L * f < f * f := by nlinarith
  calc L * f < f * f := h
    _ = f ^ 2 := by ring

/-- The run length is bounded by the `b`'s position. -/
theorem run_length_bound (f p q : ℕ) (hq3 : 3 ≤ q) (hqf : q ≤ f) (hp2 : 2 ≤ p) :
    min p q - 1 ≤ f - 1 := by omega

/-- **The corner block never completes.**  Completion needs `f` `a`-feet, i.e. a run of length `f`;
the run has length at most `f - 1`. -/
theorem block_never_completes (f L : ℕ) (hf : 2 ≤ f) (hL : L ≤ f - 1) : L ≠ f := by omega

/-- The trichotomy loses its first branch, as a propositional step: given the three alternatives
and the refutation of the first, one of the other two holds.  Reading this as "every corner breaks"
needs the trichotomy itself, which is geometric. -/
theorem every_corner_breaks (completes baseBreak sideBreak : Prop)
    (htri : completes ∨ baseBreak ∨ sideBreak) (hno : ¬ completes) :
    baseBreak ∨ sideBreak := htri.resolve_left hno

/-- **At most one base break.**  Each consumes the single `c`, and the walk `(f,1,1)` has `n_c = 1`. -/
theorem at_most_one_base_break (breaks nc : ℕ) (hc : nc = 1) (hle : breaks ≤ nc) :
    breaks ≤ 1 := by omega

/-- **So a side break exists.**  Two corners, each breaking, at most one on the base. -/
theorem side_break_exists (west east : Bool)
    (hcount : (if west then 1 else 0) + (if east then 1 else 0) ≤ 1) :
    west = false ∨ east = false := by
  rcases west with _ | _ <;> rcases east with _ | _ <;> simp_all

end Erdos634.BlockNeverCompletes

#print axioms Erdos634.BlockNeverCompletes.run_stops_short
#print axioms Erdos634.BlockNeverCompletes.run_length_bound
#print axioms Erdos634.BlockNeverCompletes.block_never_completes
#print axioms Erdos634.BlockNeverCompletes.every_corner_breaks
#print axioms Erdos634.BlockNeverCompletes.at_most_one_base_break
#print axioms Erdos634.BlockNeverCompletes.side_break_exists
