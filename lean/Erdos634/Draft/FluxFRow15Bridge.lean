-- Draft/FluxFRow15Bridge.lean: corner counts for the target `(2α, α, 2β)`. As in
-- `Draft/FluxFRow14Bridge.lean`, the tile is the `3α + 2β = π` tile, and the corner counts follow from
-- `vertex_multiplicities`, `corner_multiplicities` and
-- `TileAt.congruentDissection_localAngle_mem` (angle-generic, not specific to a target corner value).
--
-- The three corners:
--
--   * `2α`, i.e. `(s,t) = (2,0)`: identical to the corresponding corner of the target `(2α, β, α+β)`.
--     `row14_corner_2alpha_tile` and its `Finset.card` and `CongruentDissection` wrappers do not mention
--     that target or its other corners; they are proved from the tile's relations (`hγ`, `hrel`, `hirr`)
--     and the corner-sum hypothesis `hsum : ... = 2 * α`. They are re-exported here under local names
--     (`row15_corner_2alpha_tile := Row14Bridge.row14_corner_2alpha_tile`, etc.).
--   * `α`, i.e. `(s,t) = (1,0)`: `row15_corner_alpha_tile`, by the same method (eliminate `γ`, reduce to
--     `vertex_multiplicities`, close by `omega`).
--   * `2β`, i.e. `(s,t) = (0,2)`: `row15_corner_2beta_tile`, by the same method.
--
-- Each corner has the same three-layer form as in `Row14Bridge.lean`: the arithmetic
-- `vertex_multiplicities` instance, the `Finset.card`-level `corner_multiplicities` composition, and the
-- `CongruentDissection`-level wrapper.
--
-- This file supplies corner-count infrastructure only (which tiles sit at each of the three target
-- corners, and how many). It contains no statement about the rationality of `a/c` for this target.
import Erdos634.TileAt
import Erdos634.Draft.FluxFRow14Bridge

namespace Erdos634.Row15Bridge

open Erdos634.Geometry Erdos634.Geometry.Dissection

variable {N : ℕ}

/-! ## Corner `2α`: identical to row 14's, re-exported with no new proof -/

/-- **A `2α`-corner fills uniquely as two `α`-tiles** (row 15's first target corner). Verbatim
`Row14Bridge.row14_corner_2alpha_tile` — the underlying lemma never mentions which row's target the
corner belongs to, only the tile's own relations and the corner-sum hypothesis, so it applies here
unchanged. -/
theorem row15_corner_2alpha_tile {α β γ : ℝ} (hγ : γ = 2 * α + β)
    (hrel : 3 * α + 2 * β = Real.pi) (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (p q r s : ℕ)
    (hsum : (p : ℝ) * α + (q : ℝ) * β + (r : ℝ) * γ + (s : ℝ) * Real.pi = 2 * α) :
    p = 2 ∧ q = 0 ∧ r = 0 ∧ s = 0 :=
  Row14Bridge.row14_corner_2alpha_tile hγ hrel hirr p q r s hsum

/-- **Exactly two `α`-tiles at a `2α` corner, no `β`, `γ`, or straight-angle tile** — the
`Finset.card`-level count, row 15's first target corner. Verbatim `Row14Bridge.row14_corner_2alpha_counts`. -/
theorem row15_corner_2alpha_counts {N : ℕ} (D : Dissection N) (α β γ : ℝ)
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
    ({i | (D.tile i).localAngle (D.target.pts k) = Real.pi} : Finset (Fin N)).card = 0 :=
  Row14Bridge.row14_corner_2alpha_counts D α β γ hαβ hαγ hαπ hα0 hβγ hβπ hβ0 hγπ hγ0 hπ0
    hγdef hrel hirr k hvals hcorner

/-- **A `2α` corner of a real congruent dissection (row 15's target, first corner) fills uniquely
as two `α`-tiles.** Verbatim `Row14Bridge.congruentDissection_row14_2alpha_counts`. -/
theorem congruentDissection_row15_2alpha_counts (D : CongruentDissection N) (α β γ : ℝ)
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
  Row14Bridge.congruentDissection_row14_2alpha_counts D α β γ hαβ hαγ hαπ hα0 hβγ hβπ hβ0 hγπ hγ0
    hπ0 hγdef hrel hirr hα' hβ' hγ' k hcorner

/-! ## Corner `α`: genuinely new, `(s,t) = (1,0)` -/

/-- **An `α`-corner fills uniquely as one `α`-tile.** Same method as `TilePlacement.apex_counts`
(target `3α`) and `Row14Bridge.row14_corner_2alpha_tile` (target `2α`), instantiated at
`(s,t) = (1,0)`. -/
theorem row15_corner_alpha_tile {α β γ : ℝ} (hγ : γ = 2 * α + β)
    (hrel : 3 * α + 2 * β = Real.pi) (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (p q r s : ℕ)
    (hsum : (p : ℝ) * α + (q : ℝ) * β + (r : ℝ) * γ + (s : ℝ) * Real.pi = α) :
    p = 1 ∧ q = 0 ∧ r = 0 ∧ s = 0 := by
  rw [hγ, ← hrel] at hsum
  have h' : (p : ℝ) * α + (q : ℝ) * β + (r : ℝ) * (2 * α + β)
      = ((1 - 3 * (s : ℤ) : ℤ) : ℝ) * α + ((-2 * (s : ℤ) : ℤ) : ℝ) * β := by
    push_cast
    linarith [hsum]
  obtain ⟨h1, h2⟩ := Erdos634.Geometry.vertex_multiplicities hrel hirr p q r _ _ h'
  refine ⟨by omega, by omega, by omega, by omega⟩

/-- **Exactly one `α`-tile at an `α` corner, no `β`, `γ`, or straight-angle tile.** -/
theorem row15_corner_alpha_counts {N : ℕ} (D : Dissection N) (α β γ : ℝ)
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hαπ : α ≠ Real.pi) (hα0 : α ≠ 0)
    (hβγ : β ≠ γ) (hβπ : β ≠ Real.pi) (hβ0 : β ≠ 0)
    (hγπ : γ ≠ Real.pi) (hγ0 : γ ≠ 0) (hπ0 : Real.pi ≠ 0)
    (hγdef : γ = 2 * α + β) (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (k : Fin 3)
    (hvals : ∀ i, (D.tile i).localAngle (D.target.pts k)
      ∈ ({α, β, γ, Real.pi, 0} : Finset ℝ))
    (hcorner : cornerAngle (D.target.pts (k + 1)) (D.target.pts k) (D.target.pts (k + 2)) = α) :
    ({i | (D.tile i).localAngle (D.target.pts k) = α} : Finset (Fin N)).card = 1 ∧
    ({i | (D.tile i).localAngle (D.target.pts k) = β} : Finset (Fin N)).card = 0 ∧
    ({i | (D.tile i).localAngle (D.target.pts k) = γ} : Finset (Fin N)).card = 0 ∧
    ({i | (D.tile i).localAngle (D.target.pts k) = Real.pi} : Finset (Fin N)).card = 0 := by
  have h := Erdos634.TilePlacement.corner_multiplicities D α β γ hαβ hαγ hαπ hα0 hβγ hβπ hβ0
    hγπ hγ0 hπ0 k hvals
  rw [hcorner] at h
  exact row15_corner_alpha_tile hγdef hrel hirr _ _ _ _ h

/-- **An `α` corner of a real congruent dissection (row 15's target, second corner) fills uniquely
as one `α`-tile.** -/
theorem congruentDissection_row15_alpha_counts (D : CongruentDissection N) (α β γ : ℝ)
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hαπ : α ≠ Real.pi) (hα0 : α ≠ 0)
    (hβγ : β ≠ γ) (hβπ : β ≠ Real.pi) (hβ0 : β ≠ 0)
    (hγπ : γ ≠ Real.pi) (hγ0 : γ ≠ 0) (hπ0 : Real.pi ≠ 0)
    (hγdef : γ = 2 * α + β) (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (hα' : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hβ' : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hγ' : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    (k : Fin 3)
    (hcorner : cornerAngle (D.target.pts (k + 1)) (D.target.pts k) (D.target.pts (k + 2)) = α) :
    ({i | (D.tile i).localAngle (D.target.pts k) = α} : Finset (Fin N)).card = 1 ∧
    ({i | (D.tile i).localAngle (D.target.pts k) = β} : Finset (Fin N)).card = 0 ∧
    ({i | (D.tile i).localAngle (D.target.pts k) = γ} : Finset (Fin N)).card = 0 ∧
    ({i | (D.tile i).localAngle (D.target.pts k) = Real.pi} : Finset (Fin N)).card = 0 :=
  row15_corner_alpha_counts D.toDissection α β γ hαβ hαγ hαπ hα0 hβγ hβπ hβ0 hγπ hγ0 hπ0
    hγdef hrel hirr k
    (fun i => congruentDissection_localAngle_mem D α β γ hα' hβ' hγ' k i) hcorner

/-! ## Corner `2β`: genuinely new, `(s,t) = (0,2)` -/

/-- **A `2β`-corner fills uniquely as two `β`-tiles.** Same method, instantiated at
`(s,t) = (0,2)`. -/
theorem row15_corner_2beta_tile {α β γ : ℝ} (hγ : γ = 2 * α + β)
    (hrel : 3 * α + 2 * β = Real.pi) (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (p q r s : ℕ)
    (hsum : (p : ℝ) * α + (q : ℝ) * β + (r : ℝ) * γ + (s : ℝ) * Real.pi = 2 * β) :
    p = 0 ∧ q = 2 ∧ r = 0 ∧ s = 0 := by
  rw [hγ, ← hrel] at hsum
  have h' : (p : ℝ) * α + (q : ℝ) * β + (r : ℝ) * (2 * α + β)
      = ((-3 * (s : ℤ) : ℤ) : ℝ) * α + ((2 - 2 * (s : ℤ) : ℤ) : ℝ) * β := by
    push_cast
    linarith [hsum]
  obtain ⟨h1, h2⟩ := Erdos634.Geometry.vertex_multiplicities hrel hirr p q r _ _ h'
  refine ⟨by omega, by omega, by omega, by omega⟩

/-- **Exactly two `β`-tiles at a `2β` corner, no `α`, `γ`, or straight-angle tile.** -/
theorem row15_corner_2beta_counts {N : ℕ} (D : Dissection N) (α β γ : ℝ)
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hαπ : α ≠ Real.pi) (hα0 : α ≠ 0)
    (hβγ : β ≠ γ) (hβπ : β ≠ Real.pi) (hβ0 : β ≠ 0)
    (hγπ : γ ≠ Real.pi) (hγ0 : γ ≠ 0) (hπ0 : Real.pi ≠ 0)
    (hγdef : γ = 2 * α + β) (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (k : Fin 3)
    (hvals : ∀ i, (D.tile i).localAngle (D.target.pts k)
      ∈ ({α, β, γ, Real.pi, 0} : Finset ℝ))
    (hcorner : cornerAngle (D.target.pts (k + 1)) (D.target.pts k) (D.target.pts (k + 2))
      = 2 * β) :
    ({i | (D.tile i).localAngle (D.target.pts k) = α} : Finset (Fin N)).card = 0 ∧
    ({i | (D.tile i).localAngle (D.target.pts k) = β} : Finset (Fin N)).card = 2 ∧
    ({i | (D.tile i).localAngle (D.target.pts k) = γ} : Finset (Fin N)).card = 0 ∧
    ({i | (D.tile i).localAngle (D.target.pts k) = Real.pi} : Finset (Fin N)).card = 0 := by
  have h := Erdos634.TilePlacement.corner_multiplicities D α β γ hαβ hαγ hαπ hα0 hβγ hβπ hβ0
    hγπ hγ0 hπ0 k hvals
  rw [hcorner] at h
  exact row15_corner_2beta_tile hγdef hrel hirr _ _ _ _ h

/-- **A `2β` corner of a real congruent dissection (row 15's target, third corner) fills uniquely
as two `β`-tiles.** -/
theorem congruentDissection_row15_2beta_counts (D : CongruentDissection N) (α β γ : ℝ)
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
      = 2 * β) :
    ({i | (D.tile i).localAngle (D.target.pts k) = α} : Finset (Fin N)).card = 0 ∧
    ({i | (D.tile i).localAngle (D.target.pts k) = β} : Finset (Fin N)).card = 2 ∧
    ({i | (D.tile i).localAngle (D.target.pts k) = γ} : Finset (Fin N)).card = 0 ∧
    ({i | (D.tile i).localAngle (D.target.pts k) = Real.pi} : Finset (Fin N)).card = 0 :=
  row15_corner_2beta_counts D.toDissection α β γ hαβ hαγ hαπ hα0 hβγ hβπ hβ0 hγπ hγ0 hπ0
    hγdef hrel hirr k
    (fun i => congruentDissection_localAngle_mem D α β γ hα' hβ' hγ' k i) hcorner

end Erdos634.Row15Bridge

#print axioms Erdos634.Row15Bridge.row15_corner_2alpha_tile
#print axioms Erdos634.Row15Bridge.row15_corner_2alpha_counts
#print axioms Erdos634.Row15Bridge.congruentDissection_row15_2alpha_counts
#print axioms Erdos634.Row15Bridge.row15_corner_alpha_tile
#print axioms Erdos634.Row15Bridge.row15_corner_alpha_counts
#print axioms Erdos634.Row15Bridge.congruentDissection_row15_alpha_counts
#print axioms Erdos634.Row15Bridge.row15_corner_2beta_tile
#print axioms Erdos634.Row15Bridge.row15_corner_2beta_counts
#print axioms Erdos634.Row15Bridge.congruentDissection_row15_2beta_counts
