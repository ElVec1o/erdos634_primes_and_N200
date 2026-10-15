import Erdos634.ForcedRow
import Erdos634.RogueChord

/-!
# Arithmetic kernels of the slot dichotomy

Two ring identities:

* the overhang of the rogue branch: `(i+1)·2(f²−e²) + ef − (i·2(f²−e²) + (2f²−e²)) = e(f−e)` (`slot_overrun_identity`);
* `(f²−e²) − f(f−e) = e(f−e)` and `f² − f(f−e) = ef` (`slot_delta_identities`).

0 sorry, standard axioms.
-/

namespace Erdos634.Draft.SlotDichotomyWrap

/-- The rogue branch overhang identity: Δ = e(f−e). -/
theorem slot_overrun_identity (e f i : ℤ) :
    ((i + 1) * (2 * (f ^ 2 - e ^ 2)) + e * f)
      - (i * (2 * (f ^ 2 - e ^ 2)) + (2 * f ^ 2 - e ^ 2)) = e * (f - e) :=
  Erdos634.ForcedRow.overrun_x e f i

/-- The two delta identities relating Δ, the chord, and ef. -/
theorem slot_delta_identities (e f : ℤ) :
    (f ^ 2 - e ^ 2) - f * (f - e) = e * (f - e) ∧
    f ^ 2 - f * (f - e) = e * f :=
  Erdos634.RogueChord.delta_identities e f

/-- Non-vacuity: both theorems are stated for all integers, trivially satisfiable. -/
theorem slot_witness : ∃ (e f : ℤ), e = 1 ∧ f = 2 :=
  ⟨1, 2, rfl, rfl⟩

#print axioms slot_overrun_identity
#print axioms slot_delta_identities

end Erdos634.Draft.SlotDichotomyWrap
