import Erdos634.BaseBetaCorners

/-!
# `b` is unsplittable: arithmetic kernel

The `b`-chord of the β-corner tile admits no subdivision into whole tile edges: the only
solution to `na·ef + nb·b + nc·f² = b` with `na,nb,nc ∈ ℕ` is `(0,1,0)`.  This is what makes the
corner parallelogram argument work.

The arithmetic is proved in `BaseBetaCorners.lean`:
- **`b_unsplittable`**: for coprime e < f with b + e² = f², `na·(ef) + nb·b + nc·f² = b`
  implies (na,nb,nc) = (0,1,0).

The same statement also appears in `ThinFamily.lean` (ℤ-typed) and
`SixtyUnsplittable.lean` (for a specific triple). The most general version is the ℕ form here.

Applying this to a real tiling requires the b-chord to be a real edge of a placed tile, which is
a tile-placement statement and is not part of this module.
-/

namespace Erdos634.Draft.BUnsplitWrap

open Erdos634.BaseBetaCorners

/-- b is unsplittable: na·(ef) + nb·b + nc·f² = b ⟹ (na,nb,nc) = (0,1,0). -/
theorem b_unsplit {e f b na nb nc : ℕ} (he : 1 ≤ e) (hef : e < f)
    (hcop : Nat.Coprime e f) (hb : b + e ^ 2 = f ^ 2)
    (heq : na * (e * f) + nb * b + nc * f ^ 2 = b) :
    na = 0 ∧ nb = 1 ∧ nc = 0 :=
  b_unsplittable e f b na nb nc he hef hcop hb heq

/-- Non-vacuity: at (e,f)=(1,2), b=3: 0·2 + 1·3 + 0·4 = 3. -/
theorem b_unsplit_witness :
    (1 : ℕ) ≤ 1 ∧ (1 : ℕ) < 2 ∧ Nat.Coprime 1 2 ∧ 3 + 1 ^ 2 = 2 ^ 2 ∧
    0 * (1 * 2) + 1 * 3 + 0 * 2 ^ 2 = 3 := by norm_num

#print axioms b_unsplit

end Erdos634.Draft.BUnsplitWrap
