import Erdos634.PinLemma
import Erdos634.PinBuffer

/-!
# Pin buffer: arithmetic cores

Four arithmetic theorems are used:

* `PinLemma.pin_forces_single_alpha`: the α-wedge is forced (x=1,y=0,z=0).
* `PinBuffer.buffer_overflow_b_is_gap`: the b-chirality gap (no x·a+y·b+z·c² = b−a).
* `PinBuffer.buffer_dichotomy`: the flank is b or c², two cases.
* `PinBuffer.overrun_amounts`: the overrun distances (b−(f−1)f = f−1, c²−(f−1)f = f).

The local geometry (that X is at the pin junction, that the flank is b or c²,
that the overrun is in the stated direction) requires the placement layer and is not part of this file.

Standard axioms, no `sorry`.
-/

namespace Erdos634.Draft.PinBufferWrap

/-- The α-wedge: if x·α + y·β + z·γ = α with 3α+2β=π, then (x,y,z)=(1,0,0). -/
theorem pin_alpha_wedge_unique {α β : ℝ}
    (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (x y z : ℕ)
    (hsum : (x : ℝ) * α + (y : ℝ) * β + (z : ℝ) * (2 * α + β) = α) :
    x = 1 ∧ y = 0 ∧ z = 0 :=
  Erdos634.PinLemma.pin_forces_single_alpha hrel hirr x y z hsum

/-- The b-chirality gap: no tile-sum equals the gap b−a. -/
theorem pin_b_chirality_gap {f a b d x y z : ℕ}
    (hf : 2 ≤ f) (ha : a = f) (hb : b + 1 = f * f) (hd : d + a = b)
    (h : x * a + y * b + z * (f * f) = d) : False :=
  Erdos634.PinBuffer.buffer_overflow_b_is_gap hf ha hb hd h

/-- The flank dichotomy: the flank is b (gap dies) or f² (overrun = (f−1)f). -/
theorem pin_flank_dichotomy {f a b : ℕ}
    (hf : 2 ≤ f) (ha : a = f) (hb : b + 1 = f * f)
    (L : ℕ) (hL : L = b ∨ L = f * f) :
    (L = b ∧ ∀ x y z : ℕ, x * a + y * b + z * (f * f) ≠ L - a) ∨
    (L = f * f ∧ L - a = (f - 1) * f) :=
  Erdos634.PinBuffer.buffer_dichotomy hf ha hb L hL

/-- The overrun amounts: b − (f−1)f = f−1 and c² − (f−1)f = f. -/
theorem pin_overrun_amounts (f : ℕ) (hf : 2 ≤ f) :
    (f * f - 1) - (f - 1) * f = f - 1 ∧ (f * f) - (f - 1) * f = f :=
  Erdos634.PinBuffer.overrun_amounts f hf

-- Non-vacuity for pin_alpha_wedge_unique: the angle sum hypothesis 3α+2β=π is satisfiable,
-- and irrationality of α/π is a number-theoretic fact about tiling members (not restated here).

#print axioms pin_alpha_wedge_unique
#print axioms pin_b_chirality_gap
#print axioms pin_flank_dichotomy
#print axioms pin_overrun_amounts

end Erdos634.Draft.PinBufferWrap
