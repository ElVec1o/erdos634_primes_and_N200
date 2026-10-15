-- Draft/FluxDRow4Bridge.lean: corner counts for the `γ = 2α` tile (angles `(α, π − 3α, 2α)`,
-- `α ∉ ℚπ`; `Draft/FluxRow4.lean`, `Draft/FluxDRow4.lean`).  The generalization of
-- `Dissection.vertex_multiplicities` (`Dissection.lean`), used unchanged by `Row14Bridge` and
-- `Row15Bridge` for the `3α+2β=π` tile family, carries over to this tile with a different defining
-- relation: eliminating the dependent angle needs one substitution instead of two.
--
-- The tile's relations are `3α + β = π`, `γ = 2α` (compare `3α + 2β = π`, `γ = 2α + β` for base-β:
-- coefficient 1 on `β` instead of 2, and `γ` a multiple of `α` instead of a combination of `α` and
-- `β`).  The existing row-4 Lean (`FluxRow4.lean`, `FluxDRow4.lean`, `FluxDRow4L8.lean`,
-- `FluxDRow4Bk.lean`) works at the side-length, law-of-sines and word level and does not use
-- vertex-figure multiplicities.
--
-- `vertex_multiplicities_row4`: given a vertex figure with `x` copies of `α`, `y` of `β = π−3α`, `z`
-- of `γ = 2α`, summing to `s·α + t·β`: substituting `γ = 2α` gives
-- `(x + 2z − s)·α + (y − t)·β = 0`; eliminating `β` via `β = π − 3α` gives
-- `(x+2z−s−3(y−t))·α + (y−t)·π = 0`, and `angle_indep` forces both integers to `0`: `y = t` and
-- `x + 2z = s`.  The proof follows that of `Dissection.vertex_multiplicities`.
--
-- Scope: the row-4 analogue is instantiated at one corner, `α`, the target's base angle
-- (`s, t = 1, 0`).  The target's other corner, the apex `π − 2α`, is a second instance of the same
-- kind (see `Draft/FluxDRow4L8.lean`).
import Erdos634.TileAt

namespace Erdos634.Row4Bridge

open Erdos634.Geometry Erdos634.Geometry.Dissection

variable {N : ℕ}

/-- **The row-4 vertex-figure bridge.**  Tile angles `α`, `β = π − 3α`, `γ = 2α`, `α ∉ ℚπ`. If a
vertex figure consists of `x` copies of `α`, `y` of `β`, `z` of `γ`, summing to `s·α + t·β`, the
multiplicities satisfy `x + 2z = s` and `y = t`.  Same method as
`Erdos634.Geometry.Dissection.vertex_multiplicities`, one relation swapped for row 4's own. -/
theorem vertex_multiplicities_row4 {α β : ℝ} (hrel : 3 * α + β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (x y z : ℕ) (s t : ℤ)
    (hsum : (x : ℝ) * α + (y : ℝ) * β + (z : ℝ) * (2 * α) = (s : ℝ) * α + (t : ℝ) * β) :
    (x : ℤ) + 2 * z = s ∧ (y : ℤ) = t := by
  have hβ : β = Real.pi - 3 * α := by linarith
  have hkey : ((((x : ℤ) + 2 * z - s) - 3 * ((y : ℤ) - t) : ℤ) : ℝ) * α
      + (((y : ℤ) - t : ℤ) : ℝ) * Real.pi = 0 := by
    rw [hβ] at hsum
    push_cast
    linear_combination hsum
  obtain ⟨hA, hB⟩ := Erdos634.Geometry.angle_indep hirr
    (((x : ℤ) + 2 * z - s) - 3 * ((y : ℤ) - t)) ((y : ℤ) - t) hkey
  omega

/-- **A base (`α`) corner of row 4's target fills uniquely as one `α`-tile.**  Instance of
`vertex_multiplicities_row4` at `(s,t) = (1,0)`, mirroring
`TilePlacement.base_corner_single_tile`'s role for base-β. -/
theorem row4_corner_alpha_tile {α β γ : ℝ} (hγ : γ = 2 * α) (hrel : 3 * α + β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (p q r s : ℕ)
    (hsum : (p : ℝ) * α + (q : ℝ) * β + (r : ℝ) * γ + (s : ℝ) * Real.pi = α) :
    p = 1 ∧ q = 0 ∧ r = 0 ∧ s = 0 := by
  rw [hγ, ← hrel] at hsum
  have h' : (p : ℝ) * α + (q : ℝ) * β + (r : ℝ) * (2 * α)
      = ((1 - 3 * (s : ℤ) : ℤ) : ℝ) * α + ((-(s : ℤ) : ℤ) : ℝ) * β := by
    push_cast
    linarith [hsum]
  obtain ⟨h1, h2⟩ := vertex_multiplicities_row4 hrel hirr p q r _ _ h'
  refine ⟨by omega, by omega, by omega, by omega⟩

/-- **Exactly one `α`-tile at row 4's base corner, no `β`, `γ`, or straight-angle tile.**  Composes
the tile-relation-agnostic `TilePlacement.corner_multiplicities` with `row4_corner_alpha_tile`,
mirroring `TilePlacement.base_corner_counts`. -/
theorem row4_corner_alpha_counts {N : ℕ} (D : Dissection N) (α β γ : ℝ)
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hαπ : α ≠ Real.pi) (hα0 : α ≠ 0)
    (hβγ : β ≠ γ) (hβπ : β ≠ Real.pi) (hβ0 : β ≠ 0)
    (hγπ : γ ≠ Real.pi) (hγ0 : γ ≠ 0) (hπ0 : Real.pi ≠ 0)
    (hγdef : γ = 2 * α) (hrel : 3 * α + β = Real.pi)
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
  exact row4_corner_alpha_tile hγdef hrel hirr _ _ _ _ h

/-- **A base (`α`) corner of a real congruent dissection by row 4's tile fills uniquely as one
`α`-tile.**  Reuses `TileAt.congruentDissection_localAngle_mem` verbatim (angle-generic; never
mentions the tile's own relation), mirroring `TileAt.congruentDissection_base_corner_counts`. -/
theorem congruentDissection_row4_alpha_counts (D : CongruentDissection N) (α β γ : ℝ)
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hαπ : α ≠ Real.pi) (hα0 : α ≠ 0)
    (hβγ : β ≠ γ) (hβπ : β ≠ Real.pi) (hβ0 : β ≠ 0)
    (hγπ : γ ≠ Real.pi) (hγ0 : γ ≠ 0) (hπ0 : Real.pi ≠ 0)
    (hγdef : γ = 2 * α) (hrel : 3 * α + β = Real.pi)
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
  row4_corner_alpha_counts D.toDissection α β γ hαβ hαγ hαπ hα0 hβγ hβπ hβ0 hγπ hγ0 hπ0
    hγdef hrel hirr k
    (fun i => congruentDissection_localAngle_mem D α β γ hα' hβ' hγ' k i) hcorner

end Erdos634.Row4Bridge

#print axioms Erdos634.Row4Bridge.vertex_multiplicities_row4
#print axioms Erdos634.Row4Bridge.row4_corner_alpha_tile
#print axioms Erdos634.Row4Bridge.row4_corner_alpha_counts
#print axioms Erdos634.Row4Bridge.congruentDissection_row4_alpha_counts
