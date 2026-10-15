-- Draft/FluxFRow14Bridge.lean: corner counts for the target `(2α, β, α+β)`. The corner-count machinery
-- behind `TileAt.congruentDissection_base_corner_counts` for the corners of the base-β target applies
-- unchanged to this target.
--
-- The target is tiled by the same tile as the base-β target: the `3α + 2β = π` tile with third angle
-- `γ = 2α + β` and `α ∉ ℚπ`. Only the target's corner angles differ (`2α, β, α+β` instead of `3α, β`).
-- The machinery is factored along this line:
--
--   * `TilePlacement.corner_multiplicities` is general: for any three distinct nonzero non-`π` angles
--     and any target corner value, it turns the angle sum at a vertex into a linear count identity.
--   * `Erdos634.Geometry.Dissection.vertex_multiplicities` is general in the target: for arbitrary
--     integers `s, t` it solves `x + 2z = s ∧ y + z = t` for the tile's multiplicities `x` (`α`-count),
--     `y` (`β`-count), `z` (`γ`-count). It uses the tile's own relations `γ = 2α + β` and
--     `3α + 2β = π`, not any property of the target.
--   * `TilePlacement.base_corner_single_tile` and `.apex_counts` are the instances of
--     `vertex_multiplicities` at `(s,t) = (0,1)` (target corner `β`) and `(s,t) = (3,0)` (target corner
--     `3α`), each closed by `omega` after nonnegativity of `p,q,r,s : ℕ` forces the unique solution.
--
-- The three corner values of the present target need the instances `(s,t) = (2,0)` (corner `2α`),
-- `(0,1)` (corner `β`, which is `base_corner_single_tile`/`base_corner_counts` unchanged), and `(1,1)`
-- (corner `α+β`). This file supplies the two missing instances (`2α` and `α+β`) at each layer at which
-- `TileAt.lean` supplies them for base-β: the arithmetic multiplicity solve, the `Finset.card`-level
-- corner count, and the `CongruentDissection`-level wrapper, which obtains the hypothesis `hvals` from
-- the general `TileAt.congruentDissection_localAngle_mem`. That lemma does not mention a target corner
-- value, only the tile's three angles, so it applies verbatim.
--
-- This file does not derive `hword` or `hF4` of `Draft/FluxFRow14.lean` (F2's word equation and F4's
-- "every side has a `c`-edge"); it supplies the corner counts those derivations need.
--
-- Other targets. For any target tiled by this same tile, each corner value `v = s·α + t·β` gets its own
-- three-line `vertex_multiplicities` instance, a `corner_multiplicities` composition and a
-- `congruentDissection_localAngle_mem` wrapper. For a tile with a different relation among its angles,
-- only `TilePlacement.corner_multiplicities` (angle-generic) is reusable, and `vertex_multiplicities`
-- would have to be reproved for that relation by the same `angle_indep`-based method.
import Erdos634.TileAt

namespace Erdos634.Row14Bridge

open Erdos634.Geometry Erdos634.Geometry.Dissection

variable {N : ℕ}

/-! ## Pure arithmetic: the two missing `vertex_multiplicities` instances

Mirrors `TilePlacement.base_corner_single_tile` (target `β`, i.e. `(s,t) = (0,1)`) and
`TilePlacement.apex_counts` (target `3α`, i.e. `(s,t) = (3,0)`) exactly. Row 14's other two target
corners are `2α` (`(s,t) = (2,0)`) and `α + β` (`(s,t) = (1,1)`); `β` itself is already covered by
`base_corner_single_tile`, reused directly below with no new arithmetic lemma. -/

/-- **A `2α`-corner fills uniquely as two `α`-tiles.**  Same method as `TilePlacement.apex_counts`
(target `3α`), instantiated at `(s,t) = (2,0)` instead of `(3,0)`. -/
theorem row14_corner_2alpha_tile {α β γ : ℝ} (hγ : γ = 2 * α + β)
    (hrel : 3 * α + 2 * β = Real.pi) (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (p q r s : ℕ)
    (hsum : (p : ℝ) * α + (q : ℝ) * β + (r : ℝ) * γ + (s : ℝ) * Real.pi = 2 * α) :
    p = 2 ∧ q = 0 ∧ r = 0 ∧ s = 0 := by
  rw [hγ, ← hrel] at hsum
  have h' : (p : ℝ) * α + (q : ℝ) * β + (r : ℝ) * (2 * α + β)
      = ((2 - 3 * (s : ℤ) : ℤ) : ℝ) * α + ((-2 * (s : ℤ) : ℤ) : ℝ) * β := by
    push_cast
    linarith [hsum]
  obtain ⟨h1, h2⟩ := Erdos634.Geometry.vertex_multiplicities hrel hirr p q r _ _ h'
  refine ⟨by omega, by omega, by omega, by omega⟩

/-- **An `(α+β)`-corner fills uniquely as one `α`-tile and one `β`-tile.**  Same method,
instantiated at `(s,t) = (1,1)`. -/
theorem row14_corner_alphabeta_tile {α β γ : ℝ} (hγ : γ = 2 * α + β)
    (hrel : 3 * α + 2 * β = Real.pi) (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (p q r s : ℕ)
    (hsum : (p : ℝ) * α + (q : ℝ) * β + (r : ℝ) * γ + (s : ℝ) * Real.pi = α + β) :
    p = 1 ∧ q = 1 ∧ r = 0 ∧ s = 0 := by
  rw [hγ, ← hrel] at hsum
  have h' : (p : ℝ) * α + (q : ℝ) * β + (r : ℝ) * (2 * α + β)
      = ((1 - 3 * (s : ℤ) : ℤ) : ℝ) * α + ((1 - 2 * (s : ℤ) : ℤ) : ℝ) * β := by
    push_cast
    linarith [hsum]
  obtain ⟨h1, h2⟩ := Erdos634.Geometry.vertex_multiplicities hrel hirr p q r _ _ h'
  refine ⟨by omega, by omega, by omega, by omega⟩

/-! ## `Finset.card`-level corner counts

Mirrors `TilePlacement.base_corner_counts`/`.apex_counts` exactly: compose the angle-generic
`corner_multiplicities` with the arithmetic instance above. -/

/-- **Exactly two `α`-tiles at a `2α` corner, no `β`, `γ`, or straight-angle tile.** -/
theorem row14_corner_2alpha_counts {N : ℕ} (D : Dissection N) (α β γ : ℝ)
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hαπ : α ≠ Real.pi) (hα0 : α ≠ 0)
    (hβγ : β ≠ γ) (hβπ : β ≠ Real.pi) (hβ0 : β ≠ 0)
    (hγπ : γ ≠ Real.pi) (hγ0 : γ ≠ 0) (hπ0 : Real.pi ≠ 0)
    (hγdef : γ = 2 * α + β) (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (k : Fin 3)
    (hvals : ∀ i, (D.tile i).localAngle (D.target.pts k)
      ∈ ({α, β, γ, Real.pi, 0} : Finset ℝ))
    (hcorner : cornerAngle (D.target.pts (k + 1)) (D.target.pts k) (D.target.pts (k + 2))
      = 2 * α) :
    ({i | (D.tile i).localAngle (D.target.pts k) = α} : Finset (Fin N)).card = 2 ∧
    ({i | (D.tile i).localAngle (D.target.pts k) = β} : Finset (Fin N)).card = 0 ∧
    ({i | (D.tile i).localAngle (D.target.pts k) = γ} : Finset (Fin N)).card = 0 ∧
    ({i | (D.tile i).localAngle (D.target.pts k) = Real.pi} : Finset (Fin N)).card = 0 := by
  have h := Erdos634.TilePlacement.corner_multiplicities D α β γ hαβ hαγ hαπ hα0 hβγ hβπ hβ0
    hγπ hγ0 hπ0 k hvals
  rw [hcorner] at h
  exact row14_corner_2alpha_tile hγdef hrel hirr _ _ _ _ h

/-- **Exactly one `α`-tile and one `β`-tile at an `α+β` corner, no `γ` or straight-angle tile.** -/
theorem row14_corner_alphabeta_counts {N : ℕ} (D : Dissection N) (α β γ : ℝ)
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hαπ : α ≠ Real.pi) (hα0 : α ≠ 0)
    (hβγ : β ≠ γ) (hβπ : β ≠ Real.pi) (hβ0 : β ≠ 0)
    (hγπ : γ ≠ Real.pi) (hγ0 : γ ≠ 0) (hπ0 : Real.pi ≠ 0)
    (hγdef : γ = 2 * α + β) (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (k : Fin 3)
    (hvals : ∀ i, (D.tile i).localAngle (D.target.pts k)
      ∈ ({α, β, γ, Real.pi, 0} : Finset ℝ))
    (hcorner : cornerAngle (D.target.pts (k + 1)) (D.target.pts k) (D.target.pts (k + 2))
      = α + β) :
    ({i | (D.tile i).localAngle (D.target.pts k) = α} : Finset (Fin N)).card = 1 ∧
    ({i | (D.tile i).localAngle (D.target.pts k) = β} : Finset (Fin N)).card = 1 ∧
    ({i | (D.tile i).localAngle (D.target.pts k) = γ} : Finset (Fin N)).card = 0 ∧
    ({i | (D.tile i).localAngle (D.target.pts k) = Real.pi} : Finset (Fin N)).card = 0 := by
  have h := Erdos634.TilePlacement.corner_multiplicities D α β γ hαβ hαγ hαπ hα0 hβγ hβπ hβ0
    hγπ hγ0 hπ0 k hvals
  rw [hcorner] at h
  exact row14_corner_alphabeta_tile hγdef hrel hirr _ _ _ _ h

/-! ## `CongruentDissection`-level: `hvals` derived, not hypothesised

Mirrors `TileAt.congruentDissection_base_corner_counts`/`.congruentDissection_apex_counts`
exactly, reusing `TileAt.congruentDissection_localAngle_mem` VERBATIM (imported, not reproved) —
that lemma never mentions a target corner value, only the tile's own three angles, so it is exactly
as valid here as it is for the base-β target. -/

/-- **A `2α` corner of a real congruent dissection (row 14's target, first corner) fills uniquely
as two `α`-tiles.** -/
theorem congruentDissection_row14_2alpha_counts (D : CongruentDissection N) (α β γ : ℝ)
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hαπ : α ≠ Real.pi) (hα0 : α ≠ 0)
    (hβγ : β ≠ γ) (hβπ : β ≠ Real.pi) (hβ0 : β ≠ 0)
    (hγπ : γ ≠ Real.pi) (hγ0 : γ ≠ 0) (hπ0 : Real.pi ≠ 0)
    (hγdef : γ = 2 * α + β) (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (hα' : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hβ' : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hγ' : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    (k : Fin 3)
    (hcorner : cornerAngle (D.target.pts (k + 1)) (D.target.pts k) (D.target.pts (k + 2))
      = 2 * α) :
    ({i | (D.tile i).localAngle (D.target.pts k) = α} : Finset (Fin N)).card = 2 ∧
    ({i | (D.tile i).localAngle (D.target.pts k) = β} : Finset (Fin N)).card = 0 ∧
    ({i | (D.tile i).localAngle (D.target.pts k) = γ} : Finset (Fin N)).card = 0 ∧
    ({i | (D.tile i).localAngle (D.target.pts k) = Real.pi} : Finset (Fin N)).card = 0 :=
  row14_corner_2alpha_counts D.toDissection α β γ hαβ hαγ hαπ hα0 hβγ hβπ hβ0 hγπ hγ0 hπ0
    hγdef hrel hirr k
    (fun i => congruentDissection_localAngle_mem D α β γ hα' hβ' hγ' k i) hcorner

/-- **An `α+β` corner of a real congruent dissection (row 14's target, third corner) fills
uniquely as one `α`-tile and one `β`-tile.** -/
theorem congruentDissection_row14_alphabeta_counts (D : CongruentDissection N) (α β γ : ℝ)
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hαπ : α ≠ Real.pi) (hα0 : α ≠ 0)
    (hβγ : β ≠ γ) (hβπ : β ≠ Real.pi) (hβ0 : β ≠ 0)
    (hγπ : γ ≠ Real.pi) (hγ0 : γ ≠ 0) (hπ0 : Real.pi ≠ 0)
    (hγdef : γ = 2 * α + β) (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (hα' : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hβ' : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hγ' : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    (k : Fin 3)
    (hcorner : cornerAngle (D.target.pts (k + 1)) (D.target.pts k) (D.target.pts (k + 2))
      = α + β) :
    ({i | (D.tile i).localAngle (D.target.pts k) = α} : Finset (Fin N)).card = 1 ∧
    ({i | (D.tile i).localAngle (D.target.pts k) = β} : Finset (Fin N)).card = 1 ∧
    ({i | (D.tile i).localAngle (D.target.pts k) = γ} : Finset (Fin N)).card = 0 ∧
    ({i | (D.tile i).localAngle (D.target.pts k) = Real.pi} : Finset (Fin N)).card = 0 :=
  row14_corner_alphabeta_counts D.toDissection α β γ hαβ hαγ hαπ hα0 hβγ hβπ hβ0 hγπ hγ0 hπ0
    hγdef hrel hirr k
    (fun i => congruentDissection_localAngle_mem D α β γ hα' hβ' hγ' k i) hcorner

-- The third corner, `β`, needs NO new declaration: `TileAt.congruentDissection_base_corner_counts`
-- already covers it verbatim (it derives from the SAME `hcorner : ... = β` shape; row 14's target
-- and the base-β target share this one corner value even though the rest of their corner sets
-- differ). Calling it out here rather than wrapping it again avoids a spurious duplicate
-- declaration.

end Erdos634.Row14Bridge

#print axioms Erdos634.Row14Bridge.row14_corner_2alpha_tile
#print axioms Erdos634.Row14Bridge.row14_corner_alphabeta_tile
#print axioms Erdos634.Row14Bridge.row14_corner_2alpha_counts
#print axioms Erdos634.Row14Bridge.row14_corner_alphabeta_counts
#print axioms Erdos634.Row14Bridge.congruentDissection_row14_2alpha_counts
#print axioms Erdos634.Row14Bridge.congruentDissection_row14_alphabeta_counts
