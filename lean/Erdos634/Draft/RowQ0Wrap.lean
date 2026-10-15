import Erdos634.ForcedRow

/-!
# The first partner and the parallelogram: arithmetic kernel

At the i-th row slot, the direct partner Q₀ closes a parallelogram
and the row top advances by exactly one base letter. The arithmetic is proved in `ForcedRow.lean`.

Key arithmetic facts:

1. **`pgram_x`**: (i+1)·2(f²−e²)+(2f²−e²) = i·2(f²−e²)+(2f²−e²) + 2(f²−e²).
   This says the row top's x-coordinate advances by 2(f²−e²) per step.
2. **`remainder_x`**: k(2f²−e²)−(2f²−e²) = (k−1)·2(f²−e²)+(k−1)·e².
3. **`overrun_x`**: the rogue overrun is e(f−e).

The statement that P₀'s a-edge is matched by a single tile Q₀ is a placement statement and is not part of this module.

0 sorry, no axioms.
-/

namespace Erdos634.Draft.RowQ0Wrap

open Erdos634.ForcedRow

/-- Parallelogram closure: row top advances by 2(f²−e²) per step. -/
theorem rowq0_pgram_x (e f i : ℤ) :
    (i + 1) * (2 * (f ^ 2 - e ^ 2)) + (2 * f ^ 2 - e ^ 2)
      = (i * (2 * (f ^ 2 - e ^ 2)) + (2 * f ^ 2 - e ^ 2)) + 2 * (f ^ 2 - e ^ 2) :=
  pgram_x e f i

/-- Remainder anchor x: k(2f²−e²)−(2f²−e²) = (k−1)·2(f²−e²)+(k−1)·e². -/
theorem rowq0_remainder_x (e f k : ℤ) :
    k * (2 * f ^ 2 - e ^ 2) - (2 * f ^ 2 - e ^ 2)
      = (k - 1) * (2 * (f ^ 2 - e ^ 2)) + (k - 1) * e ^ 2 :=
  remainder_x e f k

/-- Rogue overrun: the overrun is e(f−e). -/
theorem rowq0_overrun_x (e f i : ℤ) :
    ((i + 1) * (2 * (f ^ 2 - e ^ 2)) + e * f)
      - (i * (2 * (f ^ 2 - e ^ 2)) + (2 * f ^ 2 - e ^ 2)) = e * (f - e) :=
  overrun_x e f i

/-- Non-vacuity: at (e,f)=(1,2), i=0: check pgram_x. -/
theorem rowq0_witness : (0 + 1) * (2 * (2^2 - 1^2)) + (2*2^2 - 1^2) =
    (0 * (2 * (2^2 - 1^2)) + (2*2^2 - 1^2)) + 2 * (2^2 - 1^2) := by norm_num

#print axioms rowq0_pgram_x

end Erdos634.Draft.RowQ0Wrap
