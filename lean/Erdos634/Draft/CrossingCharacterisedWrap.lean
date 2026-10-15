import Erdos634.CrossingCharacterised

/-!
# CrossingCharacterised: crossing characterisation, wrapper

Key results:
- `no_c_before_next`: no c-edge ends at Q_{ℓ+1}
- `stretch_is_all_a`: a stretch of r a-edges gives r = f
- `crossing_iff_block_reaches`: crossing holds on all needed lines iff ℓ ≥ bp-1
- `residue_is_one_range`: the residue gap is exactly ℓ < k ≤ bp-1

No sorry, standard axioms.
-/

namespace Erdos634.Draft.CrossingCharacterisedWrap

open Erdos634.CrossingCharacterised

theorem cc2_no_c_before_next (f r s : ℕ) (hf : 3 ≤ f) (hr : 1 ≤ r)
    (h : r + s * f = f) : s = 0 :=
  no_c_before_next f r s hf hr h

theorem cc2_stretch_is_all_a (f r : ℕ) (h : r + 0 * f = f) : r = f :=
  stretch_is_all_a f r h

theorem cc2_crossing_iff_block_reaches
    (noCross : ℕ → Prop) (l bp : ℕ) (hl : 1 ≤ l)
    (holds : ∀ k, 2 ≤ k → k ≤ l → noCross k)
    (fails : ¬ noCross (l + 1)) :
    ((∀ k, 2 ≤ k → k ≤ bp - 1 → noCross k) ↔ bp - 1 ≤ l) :=
  crossing_iff_block_reaches noCross l bp hl holds fails

theorem cc2_residue_is_one_range (l bp : ℕ) :
    (∀ k, l < k → k ≤ bp - 1 → False) ↔ bp - 1 ≤ l :=
  residue_is_one_range l bp

-- Non-vacuity: l=5, bp=6 → 5 ≤ 5 ✓
example : (∀ k : ℕ, 5 < k → k ≤ 5 → False) ↔ 5 ≤ 5 := cc2_residue_is_one_range 5 6

#print axioms cc2_no_c_before_next
#print axioms cc2_crossing_iff_block_reaches

end Erdos634.Draft.CrossingCharacterisedWrap
