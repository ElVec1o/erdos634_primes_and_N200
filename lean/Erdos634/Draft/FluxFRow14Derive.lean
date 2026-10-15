-- Draft/FluxFRow14Derive.lean: F2 and part of F4 as facts about an arbitrary `CongruentDissection` of the
-- target `(2α, β, α+β)`; only universal quantification over `D` is used.
--
-- F2 (the corner-angle multiset) is assembled from the three corner-count lemmas of
-- `Draft/FluxFRow14Bridge.lean` (`congruentDissection_row14_2alpha_counts`,
-- `congruentDissection_row14_alphabeta_counts`, and `TileAt.congruentDissection_base_corner_counts` for
-- the `β` corner). F4 ("every side carries a `c`-edge") is pushed as far as the available machinery
-- reaches. The tile-generic, target-independent machinery used is `Dissection.vertex_multiplicities` and
-- `vertex_pi_multiplicities`, which encode only the relations `3α+2β=π`, `γ=2α+β`; the existence of a
-- side word comes from `EdgeWordConversion.side_walk_congruent`, which carries no multiplicity
-- information.
--
-- Closed: `row14_F2`. For an arbitrary `D : CongruentDissection N` whose target has shape
-- `(2α, β, α+β)` (with the hypotheses `hcorner1/2/3` of the lemmas of `FluxFRow14Bridge`), the tile
-- multiset at the three corners is determined: the `2α`-corner holds two α-tiles, the `β`-corner one
-- β-tile, the `(α+β)`-corner one α-tile and one β-tile. No γ occurs at any corner.
--
-- Partial: `row14_gamma_trap`. At most one γ per interior side point (`z ≤ 1` in the solution of
-- `vertex_pi_multiplicities`) is derived unconditionally for this tile. This is one of the two
-- structural ingredients of F4 (an interior point of a side holds at most one γ, since `2γ > π`).
--
-- Not closed: the full F4 (`n_c ≥ 1` on every side) needs a further ingredient not built here, a count
-- relating "each `a`- or `b`-edge tile has a γ at one of its two edge-endpoints" to "there are only
-- `n − 1` interior junction points on a side of `n` edges", i.e. an enumeration of the interior points of
-- a side as a function of the edge sequence, with an injective or counting map from the `a`,`b`-edges to
-- interior points together with corners. `EdgeWordConversion.side_walk_congruent` gives the word only as
-- an existence statement `(P,Q,R)`, with no junction positions. `GammaCount.c_edge_exists` takes the
-- analogous count (`htrap`, `hE`) as hypotheses, proved for the march boundary of the base-β target by
-- `MarchInduction` and `MarchSlots`, which does not transfer. `row14_F4` is therefore not stated as a
-- theorem here.
--
-- Consequence for `Row14.row14_rational`: its hypothesis list does not shrink. The right side of `hword`
-- (`M·(1−t)/t·s`) is fixed by Theorem 1 and the area identity, which this file does not treat; even a
-- complete F4 would discharge only `hF4`.
import Erdos634.Draft.FluxFRow14Bridge
import Erdos634.Dissection

namespace Erdos634.Row14Derive

open Erdos634.Geometry Erdos634.Geometry.Dissection Erdos634.Row14Bridge

variable {N : ℕ}

/-! ## F2 — the corner-angle-multiset fact, assembled for an arbitrary `D`

Row 14's target has corners `(2α, β, α+β)` at `k = 0, 1, 2` (matching `FluxFRow14Bridge`'s own
per-corner lemmas, which are stated corner-agnostically via an explicit `hcorner` hypothesis — this
theorem just fixes all three corners of the SAME `D` at once and conjoins the three counts). No new
geometric content beyond `FluxFRow14Bridge.lean` and `TileAt.congruentDissection_base_corner_counts`;
this is the assembly the task calls for. -/

/-- **F2 for row 14, as a fact about an arbitrary `CongruentDissection`.**  Given `D`'s three
target corners are `2α` (at `k0`), `β` (at `k1`) and `α+β` (at `k2`) — row 14's own shape, the same
hypotheses `FluxFRow14Bridge`'s lemmas take — the tile multiset at each corner is forced: no corner
holds a `γ`, and each corner's `{α, β}`-count matches the five-shapes
table specialized to `(2α, β, α+β)`. -/
theorem row14_F2 (D : CongruentDissection N) (α β γ : ℝ)
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hαπ : α ≠ Real.pi) (hα0 : α ≠ 0)
    (hβγ : β ≠ γ) (hβπ : β ≠ Real.pi) (hβ0 : β ≠ 0)
    (hγπ : γ ≠ Real.pi) (hγ0 : γ ≠ 0) (hπ0 : Real.pi ≠ 0)
    (hγdef : γ = 2 * α + β) (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (hα' : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hβ' : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hγ' : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    (k0 k1 k2 : Fin 3)
    (hcorner0 : cornerAngle (D.target.pts (k0 + 1)) (D.target.pts k0) (D.target.pts (k0 + 2))
      = 2 * α)
    (hcorner1 : cornerAngle (D.target.pts (k1 + 1)) (D.target.pts k1) (D.target.pts (k1 + 2))
      = β)
    (hcorner2 : cornerAngle (D.target.pts (k2 + 1)) (D.target.pts k2) (D.target.pts (k2 + 2))
      = α + β) :
    -- corner `k0` (angle `2α`): two α-tiles, no β, no γ
    (({i | (D.tile i).localAngle (D.target.pts k0) = α} : Finset (Fin N)).card = 2 ∧
     ({i | (D.tile i).localAngle (D.target.pts k0) = β} : Finset (Fin N)).card = 0 ∧
     ({i | (D.tile i).localAngle (D.target.pts k0) = γ} : Finset (Fin N)).card = 0) ∧
    -- corner `k1` (angle `β`): one β-tile, no α, no γ
    (({i | (D.tile i).localAngle (D.target.pts k1) = α} : Finset (Fin N)).card = 0 ∧
     ({i | (D.tile i).localAngle (D.target.pts k1) = β} : Finset (Fin N)).card = 1 ∧
     ({i | (D.tile i).localAngle (D.target.pts k1) = γ} : Finset (Fin N)).card = 0) ∧
    -- corner `k2` (angle `α+β`): one α-tile, one β-tile, no γ
    (({i | (D.tile i).localAngle (D.target.pts k2) = α} : Finset (Fin N)).card = 1 ∧
     ({i | (D.tile i).localAngle (D.target.pts k2) = β} : Finset (Fin N)).card = 1 ∧
     ({i | (D.tile i).localAngle (D.target.pts k2) = γ} : Finset (Fin N)).card = 0) := by
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨ha, hb, hg, _⟩ :=
      congruentDissection_row14_2alpha_counts D α β γ hαβ hαγ hαπ hα0 hβγ hβπ hβ0 hγπ hγ0 hπ0
        hγdef hrel hirr hα' hβ' hγ' k0 hcorner0
    exact ⟨ha, hb, hg⟩
  · obtain ⟨ha, hb, hg, _⟩ :=
      congruentDissection_base_corner_counts D α β γ hαβ hαγ hαπ hα0 hβγ hβπ hβ0
        hγπ hγ0 hπ0 hγdef hrel hirr hα' hβ' hγ' k1 hcorner1
    exact ⟨ha, hb, hg⟩
  · obtain ⟨ha, hb, hg, _⟩ :=
      congruentDissection_row14_alphabeta_counts D α β γ hαβ hαγ hαπ hα0 hβγ hβπ hβ0 hγπ hγ0 hπ0
        hγdef hrel hirr hα' hβ' hγ' k2 hcorner2
    exact ⟨ha, hb, hg⟩

/-! ## Toward F4 — the γ-trap, tile-generic

F4 needs two structural facts plus a count.  The first — "no corner
carries a γ" — is exactly `row14_F2` above (all three γ-counts are `0`).  The second — "an interior
point of the side holds at most one γ, since `2γ > π`" — is `row14_gamma_trap` below, derived
purely from `Dissection.vertex_pi_multiplicities` (tile-generic: it only encodes `3α+2β=π`,
`γ=2α+β`, never a target's corner values, so it applies to row 14's target exactly as it would to
any other target tiled by this same tile). The third ingredient — turning "at most one γ per
interior point" and "no γ at a corner" into "so `n_a+n_b ≤ n-1`, i.e. `n_c ≥ 1`" — needs a genuine
enumeration of a side's interior junction points against its edge sequence, which is NOT built
here (see the file header); `row14_F4` is consequently not stated. -/

/-- **The γ-trap, tile-generic.**  At any point where tile angles fill a straight angle
(`x·α + y·β + z·(2α+β) = π`), the γ-multiplicity is `0` or `1`, never more — the real content of
"`2γ = π + α > π`, so at most one γ per interior junction", derived here
directly from the tile's defining relations only (no target-specific input). Re-derives, for THIS
tile's own straight-angle vertex figure, the same bound `BaseBetaCorners.pi_vertex_gamma_le_one`
supplies for the march's boundary-layer target — this file's version depends on nothing but
`Dissection.vertex_pi_multiplicities`, so it is available for row 14 (and any other target sharing
this tile) without redoing the march's own corner-rule machinery. -/
theorem row14_gamma_trap {α β : ℝ} (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (x y z : ℕ)
    (hsum : (x : ℝ) * α + (y : ℝ) * β + (z : ℝ) * (2 * α + β) = Real.pi) :
    z ≤ 1 := by
  obtain ⟨h1, h2⟩ := Erdos634.Geometry.vertex_pi_multiplicities hrel hirr x y z hsum
  omega

end Erdos634.Row14Derive

#print axioms Erdos634.Row14Derive.row14_F2
#print axioms Erdos634.Row14Derive.row14_gamma_trap
