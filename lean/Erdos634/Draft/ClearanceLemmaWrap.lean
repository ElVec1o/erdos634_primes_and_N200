import Erdos634.ClearanceLemma

/-!
# Clearance ratio: wrapper

Re-exports results of `ClearanceLemma`:
- `altitude_ge_min_X`: altitude to side `s` is at least `2A/c` when `s ≤ c`.
- `clearance_ratio_base_X`: base clearance ratio `h_min/H = e/f²`.
- `clearance_ratio_leg_X`: leg clearance ratio `h_min/d = f/N`.
- `refined_leg_exclusion_iff_X`: refined leg chord falls below floor iff `e²N < f³`.

No `sorry`; standard axioms only.
-/

namespace Erdos634.Draft.ClearanceLemmaWrap
open Erdos634.ClearanceLemma

/-- Wrap: the altitude to any side is at least `2A/c` when that side is the longest. -/
theorem altitude_ge_min_X {A s c : ℚ} (hA : 0 < A) (hs : 0 < s) (hsc : s ≤ c) :
    2 * A / c ≤ 2 * A / s :=
  altitude_ge_min hA hs hsc

/-- Wrap: base clearance ratio `(2A/f²) / (2A/e) = e/f²`. -/
theorem clearance_ratio_base_X {A e f : ℚ} (hA : A ≠ 0) (he : e ≠ 0) (hf : f ≠ 0) :
    (2 * A / f ^ 2) / (2 * A / e) = e / f ^ 2 :=
  clearance_ratio_base hA he hf

/-- Wrap: leg clearance ratio `(2A/f²) / (2NA/f³) = f/N`. -/
theorem clearance_ratio_leg_X {A f N : ℚ} (hA : A ≠ 0) (hf : f ≠ 0) (hN : N ≠ 0) :
    (2 * A / f ^ 2) / (2 * N * A / f ^ 3) = f / N :=
  clearance_ratio_leg hA hf hN

/-- Wrap: the refined leg chord falls below the floor exactly when `e²N < f³`. -/
theorem refined_leg_exclusion_iff_X {e f N : ℚ} (hf : 0 < f) (hN : 0 < N)
    (hNdef : N = 3 * f ^ 2 - e ^ 2) :
    f ^ 3 * (N - f) / N < f * (f ^ 2 - e ^ 2) ↔ e ^ 2 * N < f ^ 3 :=
  refined_leg_exclusion_iff hf hN hNdef

-- Non-vacuity: `e = 1, f = 2` satisfies the side-length ordering
example : (1 : ℚ) * 2 ≤ 2 ^ 2 ∧ 2 ^ 2 - 1 ^ 2 ≤ 2 ^ 2 := by norm_num

#print axioms altitude_ge_min_X
#print axioms clearance_ratio_base_X
#print axioms clearance_ratio_leg_X
#print axioms refined_leg_exclusion_iff_X
end Erdos634.Draft.ClearanceLemmaWrap
