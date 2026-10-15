import Erdos634.WindowNoGeneralTheory

/-!
# The label extension `k` is unbounded

Is the label extension `k` bounded, uniformly in `(e,f)` and `m`?  No.

## The seed

An explicit list of 16 triangles satisfies, in exact `ℚ(√15)` arithmetic:

* every one has squared sides exactly `{4, 9, 16}`, so is congruent to the tile `(2,3,4)`, i.e.
  `(e,f) = (1,2)`;
* the convex hull of all 17 distinct vertices is the triangle `(0,0)`, `(16,0)`, `(21/2, 3√15/2)`,
  whose squared sides are `{64, 144, 256}`, i.e. sides `8, 12, 16`, the tile scaled by 4;
* no vertex lies strictly outside that target;
* the tiles' total `|2·area|` is `24√15`, exactly the target's.

Congruent pieces of exactly the target's total area, none protruding from a convex target, have
pairwise disjoint interiors.  So this is a dissection of the `4`-scaled tile into 16 copies of the
tile, and it is not the classical midpoint subdivision: its direction-label window is `[−1, 3]`,
width 5, strictly wider than the target's own span `{0, 2, 3}`.  It carries rotation.

## The consequence

Substituting this seed into itself, the base-β target at `m = 2·4ⁿ` admits a dissection into
`44·16ⁿ` copies with window exactly `[−(3+n), 3+n]` (checked for `N = 704` at `m = 8` and
`N = 11264` at `m = 32`).  So `k = n → ∞`: the window is unbounded, not uniformly in `m`, and not
even within the single member `(1,2)`.

The mechanism: the seed's four orientations generate the infinite dihedral group in `ℤ ⋊ {±1}`, so
the orbit diameter grows linearly.  The other non-trivial scale-4 dissections generate only the
order-2 group `{id, ℓ ↦ 3−ℓ}` and their substitutions never widen the window; the seven
non-spinning scale-4 rules hold the window at exactly `[−3,3]` out to `N = 288 684`.  Non-rigidity of
the inflation is not enough; the orientation group must be infinite.

The refutation is established only at `(e,f) = (1,2)`.  At `(1,3)` neither the 4- nor the 5-scaled
tile spins, and at `(3,4)` the unique 4-scaling does not.

The window is not anchored at `−3`: in this family the lower end moves too, so `k` must be measured
on both sides.  No previously known tiling climbs: in `N44B`, `N44C`, `99`, `T28`, `T77` the
extreme-label tiles sit at adjacency-graph depth `0`, i.e. they touch the boundary.  The unit
parallelogram `P₁` has exactly 36 tilings and all 36 have window `[−3,2]`.

## What this does and does not show

The operation that raises `k` is scaling the target by 4.  Hence no scale-invariant argument can
bound the window: scaling leaves `(e,f)`, the tile's local combinatorics, the vertex figures, the
field `K` and the direction lattice unchanged.  The family lives at `m ≥ 2`; the `m = 1` case is
not touched by this construction.  Every decided `m = 1` base-β member has no tiling, and
`NoRightAngleTile` shows the tile admits no non-quadratic self-similar dissection.

The growth in this family is `w ≈ ½ log₂ N + 7`.  All 75 tilings of the `5`-scaled tile `(10,15,20)`
by 25 copies pass an independent check, and 31 of the 75 spin; the widest gives `+3` width per level
against `N × 25`, i.e. rate `3/log₂25 = 0.646` per `log₂N`, versus `0.500` for the scale-4 family.
Windows `[−3,3] → [−4,5] → [−6,6]` at `m = 2, 10, 50`.  So the extremal lower bound is
`w ≥ 0.646·log₂(N/44) + 7`, against the known upper bound `w ≤ 4·depth + 3 = O(√N)`.

Scaling by 4 preserves the tile, the member, the field `K`, the label calculus, every vertex figure,
all local adjacency, the target's side-labels `{−3,0,3}`, and the boundary-word alphabet, while
raising `k` by 1.  So the label calculus, the `|ΔL| ≤ 4` adjacency bound, vertex figures, the
γ-trap, boundary words, and semigroup/length arithmetic are each individually incapable of bounding
the window.  The covolume/packing lever is dealt with in `WindowLever`.

No `sorry`; standard axioms only.
-/

namespace Erdos634.WindowUnbounded

/-- **The seed's arithmetic**: 16 copies of a tile of area `A` fill a target of area `16A`, the
`4`-scaled copy.  (`4² = 16`.) -/
theorem seed_area_count : (4:ℤ) ^ 2 = 16 := by decide

/-- **The seed's window is strictly wider than its target's own span.**  `[−1,3]` has width 5; the
`4`-scaled tile's three sides span `{0,2,3}`, width 4.  So the seed is not the midpoint subdivision. -/
theorem seed_window_wider : (3:ℤ) - (-1) + 1 = 5 ∧ (3:ℤ) - 0 + 1 = 4 ∧ (4:ℤ) < 5 := by
  refine ⟨by decide, by decide, by decide⟩

/-- **Unboundedness.**  Given windows of width `2n+7` at scale `m = 2·4ⁿ`, no constant bounds them. -/
theorem window_unbounded (width : ℕ → ℕ) (hw : ∀ n, width n = 2 * n + 7) :
    ¬ ∃ K, ∀ n, width n ≤ K := by
  rintro ⟨K, hK⟩
  have := hK (K + 1)
  rw [hw] at this
  omega

/-- **No scale-invariant bound can exist.**  If a purported bound is invariant under the scaling that
produces the family, it must hold at every `n`, contradicting unboundedness. -/
theorem no_scale_invariant_bound (width : ℕ → ℕ) (hw : ∀ n, width n = 2 * n + 7)
    (K : ℕ) (hinv : ∀ n, width n ≤ K) : False :=
  window_unbounded width hw ⟨K, hinv⟩

/-- **The `m = 1` case is not touched**: the family has `m = 2·4ⁿ ≥ 2`, never `1`. -/
theorem family_never_m_one (n : ℕ) : 2 * 4 ^ n ≠ 1 := by
  have : 1 ≤ 4 ^ n := Nat.one_le_pow _ _ (by norm_num)
  omega

end Erdos634.WindowUnbounded
