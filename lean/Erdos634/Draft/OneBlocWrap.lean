import Erdos634.CChord

/-!
# One-end-blocked chord dichotomy: arithmetic kernel

If exactly one end of the chord is blocked, the chord is either
a single `c`-edge or (at `e = 1`) an `f`-fold `a`-run.  The full claim requires a "far side of
the chord" placement statement; the arithmetic dichotomy itself is:

`x·a + y·b + z·c = c` (chord covered by nonneg integer multiples of the three sides) implies
either `(x,y,z) = (0,0,1)` (the chord is a single `c`-edge) or `e = 1 ∧ (x,y,z) = (f,0,0)`
(at the Pythagorean subfamily, the chord is `f` consecutive `a`-edges).

The arithmetic content is in `CChord.lean`:

1. **`c_chord_dichotomy`**: given coprime `1 ≤ e < f` and tile sides `a = ef`, `b = f²−e²`,
   `c = f²`, and `x·a + y·b + z·c = c`, exactly `(x,y,z) = (0,0,1)` or `e = 1` with
   `(x,y,z) = (f,0,0)`. Proved by an interval case-split on `z` plus divisibility arithmetic.

The placement statement (the far side of the chord in the ambient tiling) is not part of this file.
Standard axioms, no `sorry`.
-/

namespace Erdos634.Draft.OneBlocWrap

open Erdos634.CChord

/-- One-end-blocked chord (CChord form): if x·a + y·b + z·c = c with a=ef, b+e²=f², c=f²,
    coprime 1≤e<f, then (x,y,z) = (0,0,1) or e = 1 with (x,y,z) = (f,0,0). -/
theorem one_bloc_chord_dichotomy {e f b : ℕ}
    (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f)
    (hb : b + e * e = f * f)
    {x y z : ℕ} (h : x * (e * f) + y * b + z * (f * f) = f * f) :
    (x = 0 ∧ y = 0 ∧ z = 1) ∨ (e = 1 ∧ x = f ∧ y = 0 ∧ z = 0) :=
  c_chord_dichotomy hco he hef rfl hb rfl h

/-- Non-vacuity: at (e,f,b) = (1,2,3): b + 1² = 2², single-c solution (0,0,1). -/
theorem one_bloc_witness_single_c :
    (3 : ℕ) + 1 * 1 = 2 * 2 ∧ (0 : ℕ) * (1 * 2) + 0 * 3 + 1 * (2 * 2) = 2 * 2 := by norm_num

/-- Non-vacuity: at (e,f,b) = (1,2,3): f-fold a-run solution (2,0,0). -/
theorem one_bloc_witness_a_run :
    (3 : ℕ) + 1 * 1 = 2 * 2 ∧ (2 : ℕ) * (1 * 2) + 0 * 3 + 0 * (2 * 2) = 2 * 2 := by norm_num

#print axioms one_bloc_chord_dichotomy

end Erdos634.Draft.OneBlocWrap
