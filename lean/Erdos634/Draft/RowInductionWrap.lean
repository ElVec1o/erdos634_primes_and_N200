import Erdos634.ForcedRow

/-!
# The induction step of the row argument: wrapper

If every slot of Δ_k takes the std branch, the first row is the standard one: P₀,…,P_{k-1} and Q₀,…,Q_{k-2}, 2k−1 tiles,
and the closure of Δ_k minus the row is the scale-(k−1) occurrence anchored at A+c·u (`ForcedRow.remainder_x/y`; the count
(2k−1)+(k−1)² = k² is `ForcedRow.row_count`).  Hence W(k−1) ⇒ W(k) holds whenever every slot's
rogue branch is refuted, and the whole tower {W(k) : k ≤ f} closes when this happens at every scale.

Lean content:
1. **`rowinduction_row_count`**: tile count identity (2k−1) + (k−1)² = k² (`ForcedRow.row_count`).
2. **`rowinduction_remainder_x`**: x-coordinate of the remainder region (`ForcedRow.remainder_x`).
3. **`rowinduction_remainder_y`**: y-coordinate of the remainder region (`ForcedRow.remainder_y`).
4. **`rowinduction_slot_dies`**: a slot with rogue overhang dies by containment
   (`ForcedRow.slot_dies_by_containment`).
5. **`rowinduction_rogue_overrun_pos`**: the rogue overhang is positive (`ForcedRow.rogue_overrun_pos`).

All statements are arithmetic.  0 sorry, standard axioms.
-/

namespace Erdos634.Draft.RowInductionWrap

open Erdos634.ForcedRow

/-- cor:rowinduction (count): (2k−1) + (k−1)² = k² (row_count). -/
theorem rowinduction_row_count (k : ℤ) : (2 * k - 1) + (k - 1) ^ 2 = k ^ 2 :=
  row_count k

/-- cor:rowinduction (remainder x): x-coordinate of the remainder region (remainder_x). -/
theorem rowinduction_remainder_x (e f k : ℤ) :
    k * (2 * f ^ 2 - e ^ 2) - (2 * f ^ 2 - e ^ 2)
      = (k - 1) * (2 * (f ^ 2 - e ^ 2)) + (k - 1) * e ^ 2 :=
  remainder_x e f k

/-- cor:rowinduction (remainder y): y-coordinate identity for the remainder (remainder_y). -/
theorem rowinduction_remainder_y (e k : ℤ) : k * e - e = (k - 1) * e :=
  remainder_y e k

/-- cor:rowinduction (slot dies): at slot i with (i+1)·e < f the rogue exits Δ_k
(slot_dies_by_containment). -/
theorem rowinduction_slot_dies (i e f : ℤ) (hef : e < f) (he : 0 < e)
    (h : (i + 1) * e < f) : (f ^ 2 - e ^ 2) * ((i + 1) * e - f) < 0 :=
  slot_dies_by_containment i e f hef he h

/-- cor:rowinduction (rogue overrun positive): chordLen std < chordLen rogue (rogue_overrun_pos). -/
theorem rowinduction_rogue_overrun_pos (e f : ℕ) (he : 1 ≤ e) (hef : e < f) :
    SlotChoice.chordLen e f SlotChoice.std < SlotChoice.chordLen e f SlotChoice.rogue :=
  rogue_overrun_pos e f he hef

#print axioms rowinduction_row_count
#print axioms rowinduction_remainder_y
#print axioms rowinduction_slot_dies

end Erdos634.Draft.RowInductionWrap
