import Erdos634.TileAt

/-!
# The corner tile: wrapper

The corner tile of the base-β family is unique and presents
angle β at the base corner; the corner point is an actual vertex of that tile.

The content is proved in `TileAt.lean`:

1. **`congruentDissection_base_corner_tile_unique`**: given a base-β CongruentDissection,
   the target's base-corner vertex `pts k` belongs to exactly ONE tile (∃! i).

2. **`congruentDissection_base_corner_tile_vertex`**: the base-corner vertex is one of the
   three named vertices of the unique tile, and that tile presents angle β there.

0 sorry, standard axioms.
-/

namespace Erdos634.Draft.RowP0Wrap

open Erdos634.Geometry
open Erdos634.Geometry.Dissection

variable {N : ℕ}

/-- The base-corner tile is unique: exactly one tile's carrier contains the base-corner vertex. -/
theorem rowp0_corner_tile_unique (D : CongruentDissection N) (α β γ : ℝ)
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hαπ : α ≠ Real.pi) (hα0 : α ≠ 0)
    (hβγ : β ≠ γ) (hβπ : β ≠ Real.pi) (hβ0 : β ≠ 0)
    (hγπ : γ ≠ Real.pi) (hγ0 : γ ≠ 0) (hπ0 : Real.pi ≠ 0)
    (hγdef : γ = 2 * α + β) (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (hα' : Erdos634.Geometry.cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hβ' : Erdos634.Geometry.cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hγ' : Erdos634.Geometry.cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    (k : Fin 3)
    (hcorner : Erdos634.Geometry.cornerAngle (D.target.pts (k + 1)) (D.target.pts k)
        (D.target.pts (k + 2)) = β) :
    ∃! i : Fin N, D.target.pts k ∈ (D.tile i).carrier :=
  congruentDissection_base_corner_tile_unique D α β γ hαβ hαγ hαπ hα0 hβγ hβπ hβ0 hγπ hγ0 hπ0
    hγdef hrel hirr hα' hβ' hγ' k hcorner

/-- The base-corner vertex is a named vertex of the unique corner tile, presenting angle β. -/
theorem rowp0_corner_tile_vertex (D : CongruentDissection N) (α β γ : ℝ)
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hαπ : α ≠ Real.pi) (hα0 : α ≠ 0)
    (hβγ : β ≠ γ) (hβπ : β ≠ Real.pi) (hβ0 : β ≠ 0) (hβ2π : β ≠ 2 * Real.pi)
    (hγπ : γ ≠ Real.pi) (hγ0 : γ ≠ 0) (hπ0 : Real.pi ≠ 0)
    (hγdef : γ = 2 * α + β) (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (hα' : Erdos634.Geometry.cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hβ' : Erdos634.Geometry.cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hγ' : Erdos634.Geometry.cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    (k : Fin 3)
    (hcorner : Erdos634.Geometry.cornerAngle (D.target.pts (k + 1)) (D.target.pts k)
        (D.target.pts (k + 2)) = β) :
    ∃ i : Fin N, ∃ j : Fin 3, D.target.pts k = (D.tile i).pts j
      ∧ (D.tile i).localAngle (D.target.pts k) = β
      ∧ ∀ i' : Fin N, D.target.pts k ∈ (D.tile i').carrier → i' = i :=
  congruentDissection_base_corner_tile_vertex D α β γ hαβ hαγ hαπ hα0 hβγ hβπ hβ0 hβ2π hγπ hγ0
    hπ0 hγdef hrel hirr hα' hβ' hγ' k hcorner

#print axioms rowp0_corner_tile_unique
#print axioms rowp0_corner_tile_vertex

end Erdos634.Draft.RowP0Wrap
