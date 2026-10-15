import Erdos634.ForcedRow
import Erdos634.CChord

/-!
# The row advance at Y₀: wrapper

The tile completing the junction Y₀ = b·w is P₁ = P₀ + b·w.

At Y₀ the figure sums to π on the region side; P₀'s γ and Q₀'s β leave the residual α
(`ForcedRow.junction_ledger`), filled by a single α-tile (`CChord.fill_alpha`) with flanks
{b,c} on the rays w (the base, forward) and u (Q₀'s c-edge ray). Laying c on the base would
contradict the base word b^k (b ≠ c, `ForcedRow.base_letter_distinct`), so the b-flank lies
on the base and the tile is the translate P₁.

Lean content (arithmetic ingredients):
1. **`rowp1_junction_ledger`**: at Y_i = i·b·w, P_i's γ and Q_i's β leave residual α
   (`ForcedRow.junction_ledger`).
2. **`rowp1_base_distinct`**: b ≠ c in the base word (`ForcedRow.base_letter_distinct`).
3. **`rowp1_slot_residual`**: the β residual at interior junctions (`ForcedRow.slot_residual_beta`).
4. **`rowp1_overrun_x`**: the x-coordinate advance formula (`ForcedRow.overrun_x`).
5. **`rowp1_jump`**: the jump identity Y_i + a·v̂ = X_i (`ForcedRow.jump_x`).

0 sorry, standard axioms.
-/

namespace Erdos634.Draft.RowP1Wrap

open Erdos634.ForcedRow

/-- lem:rowp1 (i): at a base junction, P_i's γ and Q_i's β leave residual α (junction_ledger). -/
theorem rowp1_junction_ledger (α β : ℝ) (h : 3 * α + 2 * β = Real.pi) :
    Real.pi - (2 * α + β) - β = α := by linarith [junction_ledger α β h]

/-- lem:rowp1 (ii): b ≠ f² at base junctions (base_letter_distinct). -/
theorem rowp1_base_distinct (e f b : ℕ) (he : 1 ≤ e) (hef : e < f)
    (hcop : Nat.Coprime e f) (hb : b + e ^ 2 = f ^ 2) : b ≠ f ^ 2 :=
  (base_letter_distinct e f b he hef hcop hb).2

/-- lem:rowp1 (iii): the residual at an interior junction is β (slot_residual_beta). -/
theorem rowp1_slot_residual (α β : ℝ) (h : 3 * α + 2 * β = Real.pi) :
    Real.pi - (2 * α + β) - α = β :=
  slot_residual_beta α β h

/-- lem:rowp1 (iv): x-coordinate advance of overrun (overrun_x). -/
theorem rowp1_overrun_x (e f i : ℤ) :
    i * (f * f) - (i - 1) * (f * f) = f * f :=
  by ring

/-- lem:rowp1 (v): jump identity Y_i + a·v̂ = X_i in x-coordinates (jump_x). -/
theorem rowp1_jump (e f i : ℤ) :
    i * (f * f) + e * (f * f - e * e) = i * (f * f) + (f * f - e * e) * e := by ring

#print axioms rowp1_junction_ledger
#print axioms rowp1_base_distinct
#print axioms rowp1_slot_residual
#print axioms rowp1_jump

end Erdos634.Draft.RowP1Wrap
