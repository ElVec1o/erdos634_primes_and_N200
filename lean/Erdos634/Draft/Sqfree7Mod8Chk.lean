/-
Draft/Sqfree7Mod8Chk.lean -- two finite checks for `Sqfree7Mod8.sector_below_455`, kept in a file that does not open
`Classical` (so that `decide` finds computable instances).

* `chk_ab`: no `a < 22`, `b < 455` with `ab < 455`, `ab ≡ 7 (mod 8)`, `3 ∤ ab` and `a² + ab + b²` a perfect square;
* `chk_f2`: the only value `(a + 2b)(2a + b) < 455` with `a, b < 16`, `≡ 7 (mod 8)`, prime to `3` and
  `a² + ab + b²` a perfect square is `143`.

Composite-N plumbing.  No sorry, no native_decide.
-/
import Mathlib

set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000

namespace Erdos634.Draft.Sqfree7Mod8Chk

set_option maxRecDepth 100000 in
theorem chk_ab : ∀ a < 22, ∀ b < 455, a * b < 455 → (a * b) % 8 = 7 → 0 < (a * b) % 3 →
    Nat.sqrt (a * a + a * b + b * b) * Nat.sqrt (a * a + a * b + b * b) ≠ a * a + a * b + b * b := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem chk_f2 : ∀ a < 16, ∀ b < 16, (a + 2 * b) * (2 * a + b) < 455 → ((a + 2 * b) * (2 * a + b)) % 8 = 7 →
    0 < ((a + 2 * b) * (2 * a + b)) % 3 →
    Nat.sqrt (a * a + a * b + b * b) * Nat.sqrt (a * a + a * b + b * b) = a * a + a * b + b * b →
    (a + 2 * b) * (2 * a + b) = 143 := by
  decide +kernel

end Erdos634.Draft.Sqfree7Mod8Chk
