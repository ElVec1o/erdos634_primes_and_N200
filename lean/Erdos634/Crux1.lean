import Erdos634.A2BranchRow3
import Erdos634.PincerLadder
import Erdos634.ChordDecomp

/-!
# The `e = 1` crux: the cover of an `a`-run

## The statement

Let `e = 1`, `m = 1`, `f ≥ 3`, and let `T` be a tiling of the base-`β` target `(f³, f³, 3f² - 1)` by
the tile `(f, f² - 1, f²)`. Let `L` be an interior floor of `T` carrying a run of `f` consecutive
`a`-edges from above, a column footprint of total length `f·a = f²`. The statement considered is:

  the cover of that stretch from below is `f` `a`-edges, not a single `c`-edge.

`cover_dichotomy` proves those are the only two possibilities. In the first branch the run is
reproduced one level down and the descent continues; iterating, it reaches the base. The smallest
instance is `f = 8`, `N = 191`.

Given the statement, the chain is formalised:

* `row_three_dies_of_span`: with the descent landing, the `A₂` branch at row 3 dies, and `foot_isA`
  is not needed: `span_all_a` forces the letters under the run from the length arithmetic alone.
* `PincerLadder.first_failure_escapes`: at the first failing level `f = R + 2` the only escaping
  configurations are `(4,2)` and its mirror.
* `PincerLadder.kill_mirror`: the kills are reflection-invariant, so the mirror dies with it.
* `word42_no_landing`: `(4,2)` has no landing site at all, its longest `a`-run being `f - 2`.

`crux1_clears_a_level` below is that composition, stated on the hypotheses it consumes.

## Why counting arguments do not reach it

* Linear and character direction invariants are excluded by `LambdaFactor` (commutative ring).
* Angle-sum and Euler counting collapse to `P + T + 2I = N - 1`, giving only that the interior
  `T`-vertex count is odd, independent of the side parameter.
* The `c`-under-run configuration occurs in all eight certified tilings, and it is scale-free, so
  `ScaleRigidity.no_similarity_invariant_proof` applies to it.
* `b`-edge pairing parity forces `f` even.
* The `γ`-count: `c_under_run_dies_if_ends_gamma_free` is true but has an unsatisfiable hypothesis
  (`ends_gamma_free_impossible`), the monotone orientation word always leaving a `γ` at an endpoint.
* The `b`-residue count (`WallStraddle`) gives the number of `b`-edges on each side of a wall, but
  the locating hypothesis it needs, that a `b`-edge's endpoints are junctions on both sides, fails
  for `58` of the `60` `b`-edges in the certified tilings.

## Level lines

`ChordDecomp.area_never_integral` says the area above an interior junction chord is never an integral
number of tiles: with `N` coprime to `f` and `1 ≤ m < f²`, `f⁴ ∤ N·m²`. The horizontal level line at
level `j` has height fraction `(f-j)/f`, i.e. `m = f(f-j)`, and `1 ≤ f(f-j) < f²` exactly when
`1 ≤ j ≤ f-1`. So every interior level line has non-integral area above it
(`interior_level_area_not_integral`). The further inference that it is therefore straddled needs
`ChordTrace`'s carried covering obligation, which exists in this corpus only for the single `(3,7)`
chord. The area defect is global, while the `c`-under-run configuration lives on a stretch of the
line.

## The endpoint of an interior stretch is unconstrained

Work the vertex systems at the stretch's endpoint `P` in the `AngleArithmetic` encoding
(`α ↦ (1,0)`, `β ↦ (0,1)`, `γ = 2α+β ↦ (2,1)`, `π = 3α+2β ↦ (3,2)`), where a figure of type `(X,Y)`
solves `n_α + 2n_γ = X`, `n_β + n_γ = Y`.

* Above `P` the tiles close at `π`, type `(3,2)`: solutions `{α,α,α,β,β}` and `{γ,α,β}`.
* Below `P` the blocking `c`-tile presents `α` or `β`, `c`'s flanking angles.
  * showing `α`: the rest is `π - α`, type `(2,2)`: solutions `{α,α,β,β}` and `{γ,β}`.
  * showing `β`: the rest is `π - β`, type `(3,1)`: solutions `{α,α,α,β}` and `{γ,α}`.

Every case has two solutions (`endpoint_systems_solvable`). The half-figures above and below a
point of a line are independent, each closing at `π` on its own side, so no combination of them
contradicts, whichever angle the `c`-tile presents.

## The descent is a bounded induction

`HeightLadder.h_c = H/f²` says the blocking `c`-tile stands `1/f` of a level; the width at rung `j`
is `HeightLadder.width_at_rung_real`. A column has footprint `f²`, so it fits at rung `j` only when
`f² ≤ Y(f-j)/f`, i.e.

  `j ≤ f(2f²-1)/(3f²-1)`,  which is about `2f/3`  (`column_fits_bound`).

At `f = 8` that is `j ≤ 5`, against `9` rungs. So the descent runs at most `⌊2f/3⌋` steps, and its
last step lands on the base, where the `c`-alternative is dead: the interior feet would be vertices
interior to a boundary edge. The statement is therefore a finite induction with a proved base case,
of length about `2f/3`, in which every step is the same statement.
-/

namespace Erdos634.Crux1

open Finset

/-- **What CRUX-1 buys, composed.**  Given that the descent lands -- the run's letters occupying
`x + y + z` slots from `j`, of total length `f²`, with `f + 1` distinct junctions so `k ≥ f` -- the
`(4,2)` configuration is refuted outright, with no reach step and no fan analysis. -/
theorem crux1_clears_four_two (f B x y z j : ℕ) (hf : 3 ≤ f) (hB : B + 1 = f * f)
    (hspan : x * f + y * B + z * (B + 1) = B + 1)
    (hk : f ≤ x + y + z)
    (hfit : j + (x + y + z) ≤ f + 2)
    (hletters : ∀ i, i < x + y + z → A2BranchRow3.isA42 (j + i)) :
    False :=
  A2BranchRow3.word42_no_landing f B x y z j hf hB hspan hk hfit hletters

/-- **And `(4,2)` is the whole of a ladder level.**  At the first failing level `f = R + 2` the only
escapes are `(4,2)` and its reflection, so refuting the one refutes the level. -/
theorem four_two_is_the_level {R bp cp : ℕ} (hR : 4 ≤ R)
    (hb3 : 3 ≤ bp) (hbf : bp ≤ R + 2) (hc2 : 2 ≤ cp) (hcf : cp ≤ R + 3) (hne : bp ≠ cp)
    (hesc : ¬ PincerLadder.Kill (R + 2) bp cp R) :
    (bp = 4 ∧ cp = 2) ∨ (bp = R + 1 ∧ cp = R + 3) :=
  PincerLadder.first_failure_escapes hR hb3 hbf hc2 hcf hne hesc

/-- **Every interior level line is straddled.**  The level-`j` line has height fraction `(f-j)/f`,
so the area above it is the `m = f(f-j)` case of `ChordDecomp.area_never_integral`, and `m` lies in
`[1, f²)` exactly for `1 ≤ j ≤ f-1`.  Only the base and the apex are clean. -/
theorem interior_level_area_not_integral {N f u : ℕ} (hf : 0 < f) (hcop : Nat.Coprime N f)
    (h1 : 1 ≤ u) (h2 : u < f) : ¬ (f ^ 4 ∣ N * (f * u) ^ 2) := by
  refine ChordDecomp.area_never_integral hf hcop ?_ ?_
  · exact Nat.one_le_iff_ne_zero.mpr (by positivity)
  · have h : f * u < f * f := by nlinarith
    simpa [pow_two] using h

/-- **The endpoint of an interior stretch is unconstrained.**  Above closes at `π` (type `(3,2)`);
below, the `c`-tile shows `α` leaving `(2,2)`, or `β` leaving `(3,1)`.  All three systems are
solvable, so no local contradiction is available at the endpoint. -/
theorem endpoint_systems_solvable :
    (∃ na nb ng : ℕ, na + 2 * ng = 3 ∧ nb + ng = 2) ∧
    (∃ na nb ng : ℕ, na + 2 * ng = 2 ∧ nb + ng = 2) ∧
    (∃ na nb ng : ℕ, na + 2 * ng = 3 ∧ nb + ng = 1) :=
  ⟨⟨3, 2, 0, by omega, by omega⟩, ⟨2, 2, 0, by omega, by omega⟩, ⟨3, 1, 0, by omega, by omega⟩⟩

/-- Each of the three also has a second, `γ`-bearing solution, so the freedom is not an artefact of
picking the `γ`-free witness. -/
theorem endpoint_systems_solvable_gamma :
    (∃ na nb ng : ℕ, na + 2 * ng = 3 ∧ nb + ng = 2 ∧ ng = 1) ∧
    (∃ na nb ng : ℕ, na + 2 * ng = 2 ∧ nb + ng = 2 ∧ ng = 1) ∧
    (∃ na nb ng : ℕ, na + 2 * ng = 3 ∧ nb + ng = 1 ∧ ng = 1) :=
  ⟨⟨1, 1, 1, by omega, by omega, rfl⟩, ⟨0, 1, 1, by omega, by omega, rfl⟩,
   ⟨1, 0, 1, by omega, by omega, rfl⟩⟩

/-- **A column fits only in the lower part of the ladder.**  Footprint `f³ = f·f²` against the width
`Y(f-j)/f` at rung `j` (`HeightLadder.width_at_rung_real`) gives `f³ ≤ Y·u` with `u = f - j` and
`Y = 3f² - 1`; then `f ≤ 3u`, i.e. `j ≤ f - f/3`.  Stated additively so no truncated subtraction
appears. -/
theorem column_fits_bound (f u Y : ℕ) (hf : 3 ≤ f) (hY : Y + 1 = 3 * f ^ 2)
    (hfit : f ^ 3 ≤ Y * u) : f ≤ 3 * u := by
  by_contra h
  push_neg at h
  have h1 : 3 * u + 1 ≤ f := by omega
  nlinarith [hfit, hY, h1, hf]

end Erdos634.Crux1
