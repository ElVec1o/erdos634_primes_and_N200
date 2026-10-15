-- Draft/FluxCRow5Bridge.lean: corner counts for the equilateral target.
--
-- Part 1: the target-side corner-count bridge for the equilateral target, following the pattern that
-- `TilePlacement.corner_multiplicities` and `Dissection.vertex_multiplicities` supply for the other
-- tile families (`Draft/FluxDRow4Bridge.lean`, `Draft/FluxFRow14Bridge.lean`).
--
-- The tile of this family has third angle `γ` a rational multiple of `π` (`2π/3` or `π/3`), unlike
-- the families with `γ = 2α` or `γ = 2α + β`.  A rational-multiple-of-`π` angle can in principle give
-- a second, `α`-independent way to reach a target corner.  Here uniqueness still holds: the target
-- corner `π/3` is itself a rational multiple of `π`, and the tile relations (`α + β = π/3` or
-- `2π/3`) pin down a unique nonnegative solution once `α`'s coefficient is forced to vanish by
-- `angle_indep`; the arithmetic (`y + 2z + 3w = 1` resp. `2y + z + 3w = 1` over `ℕ`) has a unique
-- solution, unlike the `γ = π/2` case, which has two solution families.  The proofs of
-- `row5_corner_twoPiThree_tile` and `row5_corner_sixty_tile` carry out one elimination per branch.
--
-- Three layers per branch:
--   (a) pure arithmetic: a vertex figure summing to the target corner `π/3` forces the unique
--       multiplicities;
--   (b) `Finset.card` level: composing with the angle-generic `TilePlacement.corner_multiplicities`;
--   (c) `CongruentDissection` level: composing with the angle-generic
--       `TileAt.congruentDissection_localAngle_mem`.
-- The model's three corner angles equal `α`, `β`, `γ` (`hα'`/`hβ'`/`hγ'`) is taken as a hypothesis
-- rather than derived from the existential permutation in `Tri.TwoPiThreeData`/`Tri.SixtyData`, as
-- in the other bridge files.  The corner counts are not connected here to
-- `Row5.twoPiThree_forces_le_three`/`sixty_forces_not_gt_three` (`FluxCRow5Complete.lean`), which
-- consume the side decomposition `S = pa+qb+rc`.
--
-- Part 2: checks `Draft/FluxFRow14Derive.lean`'s `row14_gamma_trap` against
-- `TileAt.congruentDissection_boundary_figure_cases`.
import Erdos634.TileAt
import Erdos634.Draft.FluxCRow5

namespace Erdos634.Row5Bridge

open Erdos634.Geometry Erdos634.Geometry.Dissection

variable {N : ℕ}

/-! ## Part 1a: pure arithmetic — the two branch-specific corner instances

Row 5's two tile branches, read off `Draft/FluxCRow5.lean:151` / `Draft/FluxPaper.lean:168`:
* `2π/3` branch (`Tri.TwoPiThreeData`): angles `(α, π/3 − α, 2π/3)`, i.e. `α + β = π/3`,
  `γ = 2·(π/3)`.
* `π/3` branch (`Tri.SixtyData`, "sixty" = the paper's name for the 60° tile): angles
  `(α, 2π/3 − α, π/3)`, i.e. `α + β = 2π/3`, `γ = 1·(π/3)`.

Both branches tile an EQUILATERAL target, so every target corner is `π/3` — a single corner value
for the whole target, unlike base-β/row14/15's targets with several distinct corner values. -/

/-- **A `π/3` corner of the `2π/3`-tile target fills uniquely as one `α`-tile and one `β`-tile, no
`γ`.** The corner angle `π/3` must equal `α+β` exactly, forcing `k = l = 1, m = 0`; this is derived
here from the tile's own relation.

Elimination: `pα + qβ + rγ + sπ = π/3` with `β = π/3 − α`, `γ = 2π/3` becomes, after clearing
denominators by `3`, `3(p−q)·α + (q + 2r + 3s − 1)·π = 0`; `angle_indep` forces `p = q` and
`q + 2r + 3s = 1`, whose only solution in `ℕ` is `q = 1, r = 0, s = 0`. -/
theorem row5_corner_twoPiThree_tile {α β γ : ℝ} (hrel : α + β = Real.pi / 3)
    (hγ : γ = 2 * Real.pi / 3) (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (p q r s : ℕ)
    (hsum : (p : ℝ) * α + (q : ℝ) * β + (r : ℝ) * γ + (s : ℝ) * Real.pi = Real.pi / 3) :
    p = 1 ∧ q = 1 ∧ r = 0 ∧ s = 0 := by
  have hβ : β = Real.pi / 3 - α := by linarith
  have hkey : (((3 * (p : ℤ) - 3 * q) : ℤ) : ℝ) * α
      + (((q : ℤ) + 2 * r + 3 * s - 1 : ℤ) : ℝ) * Real.pi = 0 := by
    rw [hβ, hγ] at hsum
    push_cast
    linear_combination 3 * hsum
  obtain ⟨hA, hB⟩ := Erdos634.Geometry.angle_indep hirr
    (3 * (p : ℤ) - 3 * q) ((q : ℤ) + 2 * r + 3 * s - 1) hkey
  refine ⟨by omega, by omega, by omega, by omega⟩

/-- **A `π/3` corner of the `π/3`-tile ("sixty") target fills uniquely as one `γ`-tile, no `α` or
`β`.** The corner value coincides with the tile's OWN third angle in this branch.

Elimination: `pα + qβ + rγ + sπ = π/3` with `β = 2π/3 − α`, `γ = π/3` becomes, after clearing
denominators by `3`, `3(p−q)·α + (2q + r + 3s − 1)·π = 0`; `angle_indep` forces `p = q` and
`2q + r + 3s = 1`, whose only solution in `ℕ` is `q = 0, r = 1, s = 0` (so `p = 0` too). -/
theorem row5_corner_sixty_tile {α β γ : ℝ} (hrel : α + β = 2 * Real.pi / 3)
    (hγ : γ = Real.pi / 3) (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (p q r s : ℕ)
    (hsum : (p : ℝ) * α + (q : ℝ) * β + (r : ℝ) * γ + (s : ℝ) * Real.pi = Real.pi / 3) :
    p = 0 ∧ q = 0 ∧ r = 1 ∧ s = 0 := by
  have hβ : β = 2 * Real.pi / 3 - α := by linarith
  have hkey : (((3 * (p : ℤ) - 3 * q) : ℤ) : ℝ) * α
      + ((2 * (q : ℤ) + r + 3 * s - 1 : ℤ) : ℝ) * Real.pi = 0 := by
    rw [hβ, hγ] at hsum
    push_cast
    linear_combination 3 * hsum
  obtain ⟨hA, hB⟩ := Erdos634.Geometry.angle_indep hirr
    (3 * (p : ℤ) - 3 * q) (2 * (q : ℤ) + r + 3 * s - 1) hkey
  refine ⟨by omega, by omega, by omega, by omega⟩

/-! ## Part 1b: `Finset.card`-level corner counts

Composes the angle-generic `TilePlacement.corner_multiplicities` with the arithmetic instances
above, mirroring `Row14Bridge.row14_corner_2alpha_counts` exactly. -/

/-- **Exactly one `α`-tile and one `β`-tile at a `π/3` corner of a `2π/3`-tile dissection, no `γ`
or straight-angle tile.** -/
theorem row5_corner_twoPiThree_counts {N : ℕ} (D : Dissection N) (α β γ : ℝ)
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hαπ : α ≠ Real.pi) (hα0 : α ≠ 0)
    (hβγ : β ≠ γ) (hβπ : β ≠ Real.pi) (hβ0 : β ≠ 0)
    (hγπ : γ ≠ Real.pi) (hγ0 : γ ≠ 0) (hπ0 : Real.pi ≠ 0)
    (hrel : α + β = Real.pi / 3) (hγdef : γ = 2 * Real.pi / 3)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (k : Fin 3)
    (hvals : ∀ i, (D.tile i).localAngle (D.target.pts k)
      ∈ ({α, β, γ, Real.pi, 0} : Finset ℝ))
    (hcorner : cornerAngle (D.target.pts (k + 1)) (D.target.pts k) (D.target.pts (k + 2))
      = Real.pi / 3) :
    ({i | (D.tile i).localAngle (D.target.pts k) = α} : Finset (Fin N)).card = 1 ∧
    ({i | (D.tile i).localAngle (D.target.pts k) = β} : Finset (Fin N)).card = 1 ∧
    ({i | (D.tile i).localAngle (D.target.pts k) = γ} : Finset (Fin N)).card = 0 ∧
    ({i | (D.tile i).localAngle (D.target.pts k) = Real.pi} : Finset (Fin N)).card = 0 := by
  have h := Erdos634.TilePlacement.corner_multiplicities D α β γ hαβ hαγ hαπ hα0 hβγ hβπ hβ0
    hγπ hγ0 hπ0 k hvals
  rw [hcorner] at h
  exact row5_corner_twoPiThree_tile hrel hγdef hirr _ _ _ _ h

/-- **Exactly one `γ`-tile at a `π/3` corner of a `π/3` ("sixty") tile dissection, no `α`, `β`, or
straight-angle tile.** -/
theorem row5_corner_sixty_counts {N : ℕ} (D : Dissection N) (α β γ : ℝ)
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hαπ : α ≠ Real.pi) (hα0 : α ≠ 0)
    (hβγ : β ≠ γ) (hβπ : β ≠ Real.pi) (hβ0 : β ≠ 0)
    (hγπ : γ ≠ Real.pi) (hγ0 : γ ≠ 0) (hπ0 : Real.pi ≠ 0)
    (hrel : α + β = 2 * Real.pi / 3) (hγdef : γ = Real.pi / 3)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (k : Fin 3)
    (hvals : ∀ i, (D.tile i).localAngle (D.target.pts k)
      ∈ ({α, β, γ, Real.pi, 0} : Finset ℝ))
    (hcorner : cornerAngle (D.target.pts (k + 1)) (D.target.pts k) (D.target.pts (k + 2))
      = Real.pi / 3) :
    ({i | (D.tile i).localAngle (D.target.pts k) = α} : Finset (Fin N)).card = 0 ∧
    ({i | (D.tile i).localAngle (D.target.pts k) = β} : Finset (Fin N)).card = 0 ∧
    ({i | (D.tile i).localAngle (D.target.pts k) = γ} : Finset (Fin N)).card = 1 ∧
    ({i | (D.tile i).localAngle (D.target.pts k) = Real.pi} : Finset (Fin N)).card = 0 := by
  have h := Erdos634.TilePlacement.corner_multiplicities D α β γ hαβ hαγ hαπ hα0 hβγ hβπ hβ0
    hγπ hγ0 hπ0 k hvals
  rw [hcorner] at h
  exact row5_corner_sixty_tile hrel hγdef hirr _ _ _ _ h

/-! ## Part 1c: `CongruentDissection` level — `hvals` derived, not hypothesised

Mirrors `Row4Bridge.congruentDissection_row4_alpha_counts` /
`Row14Bridge.congruentDissection_row14_2alpha_counts` exactly, reusing
`TileAt.congruentDissection_localAngle_mem` VERBATIM (angle-generic; never mentions the tile's own
relation or the target's shape). The corner hypothesis is phrased via `D.target.angleAt k`
(`Draft/FluxTurn.lean`'s `Tri.angleAt`, definitionally `cornerAngle (D.target.pts (k+1))
(D.target.pts k) (D.target.pts (k+2))`) to match `Row5.theoremE_twoPiThree`/`_sixty`'s own `hP`
hypothesis shape (`∀ k, D.target.angleAt k = Real.pi / 3`) as closely as possible. -/

/-- **A `π/3` corner of a real congruent dissection by the `2π/3` tile fills uniquely as one
`α`-tile and one `β`-tile.** -/
theorem congruentDissection_row5_twoPiThree_counts (D : CongruentDissection N) (α β γ : ℝ)
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hαπ : α ≠ Real.pi) (hα0 : α ≠ 0)
    (hβγ : β ≠ γ) (hβπ : β ≠ Real.pi) (hβ0 : β ≠ 0)
    (hγπ : γ ≠ Real.pi) (hγ0 : γ ≠ 0) (hπ0 : Real.pi ≠ 0)
    (hrel : α + β = Real.pi / 3) (hγdef : γ = 2 * Real.pi / 3)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (hα' : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hβ' : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hγ' : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    (k : Fin 3) (hcorner : D.target.angleAt k = Real.pi / 3) :
    ({i | (D.tile i).localAngle (D.target.pts k) = α} : Finset (Fin N)).card = 1 ∧
    ({i | (D.tile i).localAngle (D.target.pts k) = β} : Finset (Fin N)).card = 1 ∧
    ({i | (D.tile i).localAngle (D.target.pts k) = γ} : Finset (Fin N)).card = 0 ∧
    ({i | (D.tile i).localAngle (D.target.pts k) = Real.pi} : Finset (Fin N)).card = 0 := by
  have hcorner' : cornerAngle (D.target.pts (k + 1)) (D.target.pts k) (D.target.pts (k + 2))
      = Real.pi / 3 := hcorner
  exact row5_corner_twoPiThree_counts D.toDissection α β γ hαβ hαγ hαπ hα0 hβγ hβπ hβ0 hγπ hγ0 hπ0
    hrel hγdef hirr k (fun i => congruentDissection_localAngle_mem D α β γ hα' hβ' hγ' k i) hcorner'

/-- **A `π/3` corner of a real congruent dissection by the `π/3` ("sixty") tile fills uniquely as
one `γ`-tile.** -/
theorem congruentDissection_row5_sixty_counts (D : CongruentDissection N) (α β γ : ℝ)
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hαπ : α ≠ Real.pi) (hα0 : α ≠ 0)
    (hβγ : β ≠ γ) (hβπ : β ≠ Real.pi) (hβ0 : β ≠ 0)
    (hγπ : γ ≠ Real.pi) (hγ0 : γ ≠ 0) (hπ0 : Real.pi ≠ 0)
    (hrel : α + β = 2 * Real.pi / 3) (hγdef : γ = Real.pi / 3)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (hα' : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hβ' : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hγ' : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    (k : Fin 3) (hcorner : D.target.angleAt k = Real.pi / 3) :
    ({i | (D.tile i).localAngle (D.target.pts k) = α} : Finset (Fin N)).card = 0 ∧
    ({i | (D.tile i).localAngle (D.target.pts k) = β} : Finset (Fin N)).card = 0 ∧
    ({i | (D.tile i).localAngle (D.target.pts k) = γ} : Finset (Fin N)).card = 1 ∧
    ({i | (D.tile i).localAngle (D.target.pts k) = Real.pi} : Finset (Fin N)).card = 0 := by
  have hcorner' : cornerAngle (D.target.pts (k + 1)) (D.target.pts k) (D.target.pts (k + 2))
      = Real.pi / 3 := hcorner
  exact row5_corner_sixty_counts D.toDissection α β γ hαβ hαγ hαπ hα0 hβγ hβπ hβ0 hγπ hγ0 hπ0
    hrel hγdef hirr k (fun i => congruentDissection_localAngle_mem D α β γ hα' hβ' hγ' k i) hcorner'

-- Non-vacuity note (per file header / `FluxCRow5Complete.lean`'s own honesty section): the
-- HYPOTHESES `hα'`/`hβ'`/`hγ'`/`hcorner` above are jointly satisfiable in the abstract (any three
-- distinct reals with the stated sum relations, e.g. `α` transcendental, `β = π/3 − α`, `γ = 2π/3`,
-- and an equilateral `D.target`), but NO REAL `CongruentDissection` witnessing them is known to
-- exist in the corpus — `Draft/FluxCRow5Witness.lean`'s own header: "no Lean dissection of an
-- equilateral target ... exists"; the smallest known real ones (1215/1440 tiles) are held only as
-- numbers. So `congruentDissection_row5_twoPiThree_counts`/`_sixty_counts` above inherit the SAME
-- paper-level conditionality as `Row5.theoremE_twoPiThree`/`_sixty` and `FluxCRow5Complete.lean`'s
-- theorems — stated here so it is not silently dropped, not a new gap.

end Erdos634.Row5Bridge

#print axioms Erdos634.Row5Bridge.row5_corner_twoPiThree_tile
#print axioms Erdos634.Row5Bridge.row5_corner_sixty_tile
#print axioms Erdos634.Row5Bridge.row5_corner_twoPiThree_counts
#print axioms Erdos634.Row5Bridge.row5_corner_sixty_counts
#print axioms Erdos634.Row5Bridge.congruentDissection_row5_twoPiThree_counts
#print axioms Erdos634.Row5Bridge.congruentDissection_row5_sixty_counts

/-! ## Part 2: comparison with `row14_gamma_trap`

`Draft/FluxFRow14Derive.lean`'s `row14_gamma_trap` states: for ARBITRARY
naturals `x, y, z` satisfying the pure algebraic equation `xα + yβ + z(2α+β) = π` (the tile
relation `3α + 2β = π`, `γ = 2α + β`), `z ≤ 1`. It is proved via
`Dissection.vertex_pi_multiplicities` (`y + z = 2 ∧ 2x + z = 3y`), then `omega`.

`TileAt.congruentDissection_boundary_figure_cases` is a DIFFERENT KIND of statement: for a REAL
`CongruentDissection D` and a REAL point `v` on the frontier of the target, not a target vertex, with
the model's own three corner angles witnessed (`hα' hβ' hγ'`), the tile-count trichotomy at `v` is
exactly `{π:1}`, `{α:3,β:2,γ:0}`, or `{α:1,β:1,γ:1}`.  It needs a `CongruentDissection` and a
specific real point as data, and its conclusion is about `Finset.card`s of tile-index sets, not about
an abstract triple of naturals `x, y, z`.

Hence `congruentDissection_boundary_figure_cases` does NOT subsume `row14_gamma_trap` as a one-line
corollary: the hypothesis of `row14_gamma_trap` (`x y z : ℕ` with the bare algebraic sum equation)
contains no `CongruentDissection`, no point, and no cardinality data.  The other direction does go
through: the trichotomy, at the `Finset.card` level, already forces the γ-count to be `0` or `1` in every
one of its three cases (`0` in the first two, `1` in the third), the real-dissection analogue of
`row14_gamma_trap`'s `z ≤ 1`, and stronger in that it names the case.  This is a one-line corollary of
`congruentDissection_boundary_figure_cases`, stated below: for any real point of a real dissection by
this tile (frontier, non-vertex), the γ-multiplicity there is at most `1`.  `row14_gamma_trap` remains
useful where no `CongruentDissection` is at hand (e.g. composed with `vertex_pi_multiplicities`
directly on a hypothesised vertex figure, as `FluxFRow14Derive.lean` does). -/

namespace Erdos634.Row14GammaTrapCorrection

open Erdos634.Geometry Erdos634.Geometry.Dissection

variable {N : ℕ}

/-- **The real-dissection analogue of `row14_gamma_trap`.** At any frontier point of the target
that is not itself a target vertex, the `γ`-tile count is at most `1` — a one-line corollary of
`congruentDissection_boundary_figure_cases`'s trichotomy, and the precise sense in which it
subsumes `row14_gamma_trap`'s content once a real `CongruentDissection` is available (see the
comment above this namespace for why it is not a literal restatement). -/
theorem congruentDissection_gamma_card_le_one (D : CongruentDissection N) (α β γ : ℝ)
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hαπ : α ≠ Real.pi) (hα0 : α ≠ 0)
    (hβγ : β ≠ γ) (hβπ : β ≠ Real.pi) (hβ0 : β ≠ 0)
    (hγπ : γ ≠ Real.pi) (hγ0 : γ ≠ 0) (hπ0 : Real.pi ≠ 0)
    (hγdef : γ = 2 * α + β) (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (hα' : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hβ' : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hγ' : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    {v : Plane} (hv : v ∈ frontier D.target.carrier) (hnv : v ∉ Set.range D.target.pts) :
    ({i | (D.tile i).localAngle v = γ} : Finset (Fin N)).card ≤ 1 := by
  rcases congruentDissection_boundary_figure_cases D α β γ hαβ hαγ hαπ hα0 hβγ hβπ hβ0 hγπ hγ0
    hπ0 hγdef hrel hirr hα' hβ' hγ' hv hnv with ⟨-, -, -, hγc⟩ | ⟨-, -, hγc⟩ | ⟨-, -, hγc⟩ <;>
    omega

end Erdos634.Row14GammaTrapCorrection

#print axioms Erdos634.Row14GammaTrapCorrection.congruentDissection_gamma_card_le_one
