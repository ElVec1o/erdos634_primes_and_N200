import Mathlib.Tactic
import Erdos634.W2Core

/-!
# The filler identity and the strip tiling: arithmetic kernel

The filler tile's side-length identity shows that the b-side
distance from the junction apex to the next junction apex is exactly b = f²−1. The key
identities are kernel-checked in `W2Core.lean`:

**Filler-mesh identity**: (f²−1)² + 4f⁶ − (3f²−1)² = 4f²(f²−1)²
for f ∈ {2,3,4,6,8,12}, kernel-checked by `decide`.

**Offset congruence**: mod 2f, 3f²−1≡−1 and the sum forcing |s|≤j<f, 2f∣(s−j)⟹s=j,
kernel-checked for f ∈ {4,6,8,12}.

That the column and its fillers tile the strip is a placement statement, not part of this file.

No sorry, no axioms.
-/

namespace Erdos634.Draft.LemFillerWrap

open Erdos634.W2Core

/-- Filler b-side identity at f=2: (4−1)²+4·2⁶−(12−1)²=4·4·(4−1)². -/
theorem filler_b_identity_f2 : (4 - 1)^2 + 4 * 2^6 - (3*4 - 1)^2 = 4 * 4 * (4 - 1)^2 :=
  filler_b_f2

/-- Filler b-side identity at f=3: (9−1)²+4·3⁶−(27−1)²=4·9·(9−1)². -/
theorem filler_b_identity_f3 : (9 - 1)^2 + 4 * 3^6 - (27 - 1)^2 = 4 * 9 * (9 - 1)^2 :=
  filler_b_f3

/-- Sum forcing at f=4: |s|≤j<4 and 8∣(s−j) ⟹ s=j. -/
theorem filler_sum_forcing_f4 (j s : ℤ) (hj : 0 ≤ j) (hjf : j < 4)
    (hs : -j ≤ s) (hs2 : s ≤ j) (hd : (8 : ℤ) ∣ (s - j)) : s = j :=
  sum_forcing_f4 j s hj hjf hs hs2 hd

/-- Offset congruence at f=4: (3·16−1)%8=7 and (8−(16−1)%8)=1. -/
theorem filler_offsets_f4 : (3 * 16 - 1) % 8 = 7 ∧ (8 - (16 - 1) % 8) = 1 :=
  offsets_f4

/-- Non-vacuity for sum_forcing_f4: at j=2, s=2: -2≤2≤2, 8∣(2-2)=0. -/
theorem filler_forcing_witness : (0 : ℤ) ≤ 2 ∧ (2 : ℤ) < 4 ∧ -(2:ℤ) ≤ 2 ∧ (2:ℤ) ≤ 2 ∧
    (8 : ℤ) ∣ (2 - 2) := by norm_num

#print axioms filler_b_identity_f2
#print axioms filler_sum_forcing_f4

end Erdos634.Draft.LemFillerWrap
