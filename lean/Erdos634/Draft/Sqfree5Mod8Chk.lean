/-
Draft/Sqfree5Mod8Chk.lean -- one finite check for `Sqfree5Mod8.f1Pair_5mod8`, kept in a file that does not open
`Classical` (so that `decide` finds computable instances).

`z64_f1`: if `A B ≡ 5 (mod 8)` (written `8 (A B) = 40` in `ZMod 64`), then `(A + B)² + 12 A B` is not a square
modulo `64`.  (Modulo `32` it always is.)  The check is split in two so that it stays small: the list of the
squares modulo `64` (`z64_sq`, 64 cases) and the values of the form (`z64_val`, 64² cases).  Deciding the
three-variable statement at once (64³ cases) would need about 11 GB.

No sorry, no native_decide.
-/
import Mathlib

set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000

namespace Erdos634.Draft.Sqfree5Mod8Chk

/-- the squares modulo `64` -/
def sq64 : List (ZMod 64) := [0, 1, 4, 9, 16, 17, 25, 33, 36, 41, 49, 57]

theorem z64_sq : ∀ W : ZMod 64, W ^ 2 ∈ sq64 := by decide

set_option maxRecDepth 100000 in
theorem z64_val : ∀ A B : ZMod 64, 8 * (A * B) = 40 → ∀ s ∈ sq64, (A + B) ^ 2 + 12 * (A * B) ≠ s := by
  decide +kernel

theorem z64_f1 : ∀ A B W : ZMod 64, 8 * (A * B) = 40 → W ^ 2 ≠ (A + B) ^ 2 + 12 * (A * B) := by
  intro A B W h hW
  exact z64_val A B h (W ^ 2) (z64_sq W) hW.symm

end Erdos634.Draft.Sqfree5Mod8Chk
