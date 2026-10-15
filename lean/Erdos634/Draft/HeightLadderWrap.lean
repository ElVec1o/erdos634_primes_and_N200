import Erdos634.HeightLadder

/-!
# HeightLadder: target height and chord width (wrapper)

Key results:
- `height_eq_twice_area`: H² = 2·Area² algebraic identity
- `run_cannot_climb`: L ≤ f and f+1 ≤ L contradict
- `chord_width`: chord endpoints identity
- `width_at_rung_real`: width at rung j identity
- `height_order`: tile heights ordered h_c < h_b < h_a

0 sorry, standard axioms.
-/

namespace Erdos634.Draft.HeightLadderWrap

open Erdos634.HeightLadder

theorem hl_height_eq_twice_area (f : ℤ) :
    4 * (f ^ 3) ^ 2 - (3 * f ^ 2 - 1) ^ 2
      = 2 * f ^ 2 * (f ^ 2 - 1) ^ 2 + 2 * (f ^ 2 - 1) ^ 2 * (f ^ 2) ^ 2
        + 2 * (f ^ 2) ^ 2 * f ^ 2 - f ^ 4 - (f ^ 2 - 1) ^ 4 - (f ^ 2) ^ 4 :=
  height_eq_twice_area f

theorem hl_run_cannot_climb (L f : ℕ) (hrun : L ≤ f) (hclimb : f + 1 ≤ L) : False :=
  run_cannot_climb L f hrun hclimb

theorem hl_chord_width (Y H h xL xR : ℤ)
    (hL : xL * (2 * H) = Y * h)
    (hR : xR * (2 * H) = 2 * Y * H - Y * h) :
    (xR - xL) * (2 * H) = 2 * Y * (H - h) :=
  chord_width Y H h xL xR hL hR

theorem hl_width_at_rung_real (Y H f j width : ℤ) (hf : 0 < f)
    (hw : width * (2 * H) = 2 * Y * (H - (j * H) / f))
    (hdvd : (f : ℤ) ∣ j * H) :
    width * f * (2 * H) = 2 * Y * (f - j) * H :=
  width_at_rung_real Y H f j width hf hw hdvd

theorem hl_height_order (f : ℤ) (hf : 2 ≤ f) : f < f ^ 2 - 1 ∧ f ^ 2 - 1 < f ^ 2 :=
  height_order f hf

-- Non-vacuity: height_eq_twice_area at f=3
example : (4 : ℤ) * (3 ^ 3) ^ 2 - (3 * 3 ^ 2 - 1) ^ 2 =
    2 * 3 ^ 2 * (3 ^ 2 - 1) ^ 2 + 2 * (3 ^ 2 - 1) ^ 2 * (3 ^ 2) ^ 2
    + 2 * (3 ^ 2) ^ 2 * 3 ^ 2 - 3 ^ 4 - (3 ^ 2 - 1) ^ 4 - (3 ^ 2) ^ 4 :=
  hl_height_eq_twice_area 3

#print axioms hl_height_eq_twice_area
#print axioms hl_width_at_rung_real

end Erdos634.Draft.HeightLadderWrap
