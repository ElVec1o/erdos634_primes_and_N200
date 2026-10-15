import Erdos634.CornerBlock

/-!
# CornerBlock: corner tile block arithmetic, wrapper

Key results:
- `block_footprint`: a-block footprint = ef²
- `block_far_side`: a-block far side = f³
- `block_counts`: f² + e² + 2(f²-e²) = 3f²-e² (total tile count closes)
- `block_far_side_eq_side_iff_m_one`: block spans corner-to-apex ↔ m=1

No sorry, standard axioms (propext, Classical.choice, Quot.sound).
-/

namespace Erdos634.Draft.CornerBlockWrap

open Erdos634.CornerBlock

theorem cb_block_footprint (e f : ℤ) : f * (e * f) = e * f ^ 2 := block_footprint e f
theorem cb_block_far_side (f : ℤ) : f * f ^ 2 = f ^ 3 := block_far_side f
theorem cb_block_counts (e f : ℤ) : f ^ 2 + e ^ 2 + 2 * (f ^ 2 - e ^ 2) = 3 * f ^ 2 - e ^ 2 :=
  block_counts e f
theorem cb_middle_is_eb (e f : ℤ) :
    e * (3 * f ^ 2 - e ^ 2) - 2 * (e * f ^ 2) = e * (f ^ 2 - e ^ 2) := middle_is_eb e f
theorem cb_block_far_side_eq_side_iff_m_one (f m : ℤ) (hf : 0 < f) :
    m * f ^ 3 = f ^ 3 ↔ m = 1 := block_far_side_eq_side_iff_m_one f m hf

-- Non-vacuity: block_counts at e=1, f=2
example : (2 : ℤ) ^ 2 + (1 : ℤ) ^ 2 + 2 * ((2 : ℤ) ^ 2 - (1 : ℤ) ^ 2) = 3 * (2 : ℤ) ^ 2 - (1 : ℤ) ^ 2 :=
  cb_block_counts 1 2

#print axioms cb_block_far_side_eq_side_iff_m_one

end Erdos634.Draft.CornerBlockWrap
