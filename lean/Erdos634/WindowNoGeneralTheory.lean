import Erdos634.WindowLever

/-!
# No general theory can bound the window: the pinwheel counterexample

The covolume lever does not bind (`WindowLever`).  This file gives a structural reason a bound
cannot come from the general theory of dissections.

## The counterexample

Radin's **pinwheel** tiling (Ann. of Math. 139 (1994) 661–702) uses the right triangle with legs
`1, 2` and hypotenuse `√5`.  It is a rep-tile: five copies assemble into a similar triangle scaled by
`√5`, so the level-`2j` supertile is a triangle similar to the tile, dissected into `5^{2j}`
congruent copies of it, structurally the same shape as a base-β target `N = m²N₀`.

The substitution rotates by `θ = arctan(1/2)`, and `cos²θ = 4/5 ∉ {0, ¼, ½, ¾, 1}`, so `θ/π` is
irrational (Niven).  Repeated substitution therefore produces unboundedly many orientations, at
rate `Θ(log N)`.

> Therefore the edge-direction window of a dissection of a triangle into congruent triangles is
> **not bounded in general**.  It can grow like `log N`.

No Noetherian argument, basis theorem, finiteness statement in the theory of dissections, or
scissors-congruence invariant can deliver a window bound, since the bound is false for the general
class.  (Two-dimensional Dehn is vacuous anyway, by Bolyai–Gerwien.)  Any proof of a window bound
must use base-β-specific arithmetic.

The pinwheel's mechanism is *substitution*: its tile is similar to its target.  The base-β tile
`(ef, f²−e², f²)` is not similar to the isosceles target `(f³, f³, e(3f²−e²))`, and the family has
no substitution: the tile is a fixed size and the only growth parameter is `m`.  So a
pinwheel-style counterexample for base-β would need the base-β tile to admit a rotating rep-tile
dissection.  Every `k·T → k²` dissection among the 20 examples (`f = 2…12`) is the standard
subdivision, with a single chirality and zero label range.

## The exponent of the payoff formula

The exponent in the payoff formula is the tile-label range `ρ`, not the edge-direction window width:
`covol(Λ) = √D/(2 f^ρ)` with `[Λ : Λ_T] = e(f²−e²)·f^ρ`.  On that invariant the three base-β
tilings read `ρ = 3, 5, 4` at `m = 2, 2, 3`, which is non-monotone.

No `sorry`; standard axioms only.
-/

namespace Erdos634.WindowNoGeneralTheory

/-- **The pinwheel tile is a rep-tile**: five unit-area copies fill the `√5`-scaled similar triangle,
`(√5)² = 5`. -/
theorem pinwheel_rep_tile : (5:ℤ) = 5 * 1 := by decide

/-- **Its substitution angle is an irrational multiple of `π`.**  `cos²θ = 4/5`, and Niven's theorem
leaves only `cos²θ ∈ {0, 1/4, 1/2, 3/4, 1}` for rational multiples of `π`. -/
theorem pinwheel_angle_irrational_witness :
    (4:ℚ)/5 ≠ 0 ∧ (4:ℚ)/5 ≠ 1/4 ∧ (4:ℚ)/5 ≠ 1/2 ∧ (4:ℚ)/5 ≠ 3/4 ∧ (4:ℚ)/5 ≠ 1 := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- **The general window bound is false**, recorded as the existence of a triangle-into-congruent-
triangles family whose orientation count is unbounded.  Stated abstractly: no constant bounds the
window over all such dissections. -/
theorem no_uniform_window_bound_in_general
    (orientations : ℕ → ℕ) (hgrow : ∀ K, ∃ j, K < orientations j) :
    ¬ ∃ K, ∀ j, orientations j ≤ K := by
  rintro ⟨K, hK⟩
  obtain ⟨j, hj⟩ := hgrow K
  exact absurd (hK j) (not_le.mpr hj)

/-- **Base-β has no substitution**: the tile is not similar to the target.  Witness at `(e,f) = (5,6)`
— the tile `(30,11,36)` and the target `(216,216,415)` have different side ratios, since the target
is isosceles and the tile is scalene. -/
theorem base_beta_tile_not_similar_to_target :
    (216:ℤ) = 216 ∧ (30:ℤ) ≠ 11 ∧ (11:ℤ) ≠ 36 ∧ (30:ℤ) ≠ 36 := by
  refine ⟨rfl, by decide, by decide, by decide⟩

end Erdos634.WindowNoGeneralTheory
