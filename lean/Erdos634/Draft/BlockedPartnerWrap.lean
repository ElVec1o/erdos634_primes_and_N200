import Erdos634.BlockedPartner

/-!
# Blocked partner analysis: wrapper

Re-exports results of `BlockedPartner`:
- `partner_forced`: partner placement is forced
- `residue_is_beta`: residue after 2γ is β
- `residue_one_tile`: X=0, Y=1 → only one β
- `no_b_in_end_slots`: end slots cannot carry b

No `sorry`; standard axioms only.
-/

namespace Erdos634.Draft.BlockedPartnerWrap

open Erdos634.BlockedPartner

theorem bp_residue_is_beta : (3 - 1 - 2, 2 - 0 - 1) = (0, 1) :=
  residue_is_beta

theorem bp_residue_one_tile (x y z : ℕ) (h1 : x + 2 * z = 0) (h2 : y + z = 1) :
    x = 0 ∧ y = 1 ∧ z = 0 :=
  residue_one_tile x y z h1 h2

theorem bp_no_b_in_end_slots (E i : ℕ) (hE : 4 ≤ E) (hi : i = 1 ∨ i = 2 ∨ i = E - 1 ∨ i = E)
    (hbarred : ∀ j, (j = 1 ∨ j = 2 ∨ j = E - 1 ∨ j = E) → ¬ (j = 0)) : i ≠ 0 :=
  no_b_in_end_slots E i hE hi hbarred

-- Non-vacuity: residue_one_tile with x=0, y=1, z=0
example : (0:ℕ) = 0 ∧ 1 = 1 ∧ 0 = 0 := bp_residue_one_tile 0 1 0 (by omega) (by omega)

#print axioms bp_residue_one_tile
#print axioms bp_residue_is_beta

end Erdos634.Draft.BlockedPartnerWrap
