import Erdos634.Inflation

/-!
# Orientation monotonicity: arithmetic kernel

On the `a`-side of a congruent dissection of the inflated tile
(or of the target's own side), the orientation sequence is `GB*BG*`: any run of `GB` tiles followed by
any run of `BG` tiles.  The forbidden pair `BG→GB` never occurs.

The arithmetic content is in `Inflation.lean`:

1. **`BG_GB_forbidden`**: `admissiblePair BG GB = false` — the transition `BG→GB` is forbidden.

2. **`orient_monotone`**: any admissible orientation sequence is of the form `GB^j ++ BG^k` for
   some `j,k`. This is the arithmetic combinatorics of the monotonicity claim.

3. **`no_two_adjacent_AAB`**: no two adjacent junctions along the `a`-run both carry `{3α,2β}`
   — the `isAAB` pattern is an independent set.

4. **`AAB_forces_alternation`**: if junction `(t₁,t₂)` is `isAAB`, the next `(t₂,t₃)` is not.

5. **`base_accounts`**: the base identity `f·a + e·b + e·c = e(3f²−e²)` for the west foot,
   middle, and east foot of the base at `m=1`.

Connecting this to a real `CongruentDissection` of the inflated tile
requires the covering-equality hypothesis, that a specific tile subset fills one occurrence `Δ_k`.
This file contains only the orientation arithmetic.

Axioms at most [propext, Classical.choice, Quot.sound]; no `sorry`.
-/

namespace Erdos634.Draft.OrientMonoWrap

open Erdos634.Inflation Erdos634.Inflation.Orient

/-- The transition BG→GB is forbidden along the a-side orientation sequence. -/
theorem orient_bg_gb_forbidden : admissiblePair BG GB = false :=
  BG_GB_forbidden

/-- Any admissible orientation sequence is GB^j ++ BG^k: first a block of GB, then BG. -/
theorem orient_sequence_monotone (L : List Orient)
    (h : L.Chain' (fun l r => admissiblePair l r = true)) :
    ∃ j k, L = List.replicate j GB ++ List.replicate k BG :=
  orient_monotone L h

/-- No two adjacent junctions both carry the {3α,2β} figure. -/
theorem orient_no_adjacent_aab (t₁ t₂ t₃ : Orient) :
    ¬(isAAB t₁ t₂ ∧ isAAB t₂ t₃) :=
  no_two_adjacent_AAB t₁ t₂ t₃

/-- An {3α,2β} junction forces the next to be non-{3α,2β}. -/
theorem orient_aab_forces_next_not_aab (t₁ t₂ t₃ : Orient) (h : isAAB t₁ t₂ = true) :
    isAAB t₂ t₃ = false :=
  AAB_forces_alternation t₁ t₂ t₃ h

/-- The base identity: f·a + e·b + e·c = e(3f²−e²) or f < e. -/
theorem orient_base_identity (e f : ℕ) :
    f * (e * f) + e * (f * f - e * e) + e * (f * f) = e * (3 * f * f - e * e) ∨ f < e :=
  base_accounts e f

/-- Non-vacuity: the {GB, BG} list satisfies admissiblePair. -/
theorem orient_witness :
    ([GB, BG] : List Orient).Chain' (fun l r => admissiblePair l r = true) := by
  simp [List.Chain', admissiblePair, rightAngle, leftAngle]

#print axioms orient_bg_gb_forbidden
#print axioms orient_sequence_monotone
#print axioms orient_no_adjacent_aab
#print axioms orient_aab_forces_next_not_aab
#print axioms orient_base_identity

end Erdos634.Draft.OrientMonoWrap
