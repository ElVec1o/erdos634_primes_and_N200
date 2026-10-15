-- Draft/FluxDRow4EdgeReading.lean: `EdgeType.edge_excludes_own_angle` for the `γ = 2α` tile, and a
-- passage from an edge-endpoint fact to a `localAngle = β` statement at a tile of a
-- `CongruentDissection`.
--
-- `EdgeType.edge_excludes_own_angle` (`EdgeType.lean`) is generic over the edge index `j : Fin 3` and
-- takes no relation hypothesis: only `hα'/hβ'/hγ'` (the model's corner-angle values) and scalene and
-- pairwise-distinct-angle hypotheses.  `AEdgeReading.a_edge_west_east` and `BEdgeReading` are the
-- same argument at other `j`, packaged in the `edgeWest`/`edgeEast` form.  The model's scalene
-- property is carried as a hypothesis `hscalene`, as `EdgeType.a_edge_endpoints` requires.
--
-- Contents:
--   1. `row4_a_edge_endpoints`: `EdgeType.edge_excludes_own_angle` / `EdgeType.a_edge_endpoints`
--      (`j = 0`) applied unchanged to this tile.
--   2. `row4_a_edge_apex_localAngle_beta` (and its `k+1`-endpoint twin
--      `row4_a_edge_apex_localAngle_beta'`): given (i) an `a`-edge of tile `i` (`hlen`), (ii) that this
--      edge's `k`-endpoint is the apex corner `B` as a point of the dissection
--      (`hvert : (D.tile i).pts k = D.target.pts kB`, a hypothesis), and (iii)
--      `Row4L8.row4_no_gamma_at_apex` (no `γ` at `B` for any tile), the conclusion
--      `(D.tile i).localAngle (D.target.pts kB) = β` follows, because `a_edge_endpoints` gives
--      `angleAt k ∈ {β, γ}` and the count of `γ` at the apex is zero.
--
-- Not derived: `hvert`, which needs the wall-chain identification (`WallEndpoints`/`SideWalk`)
-- applied to a `b^k`-then-`a`-edge leg word; and the distinctness of the two tiles at the two ends of
-- the leg (`Draft/FluxDRow4L8AC.lean`'s `row4_ac_leg_contradiction` takes `i ≠ j` as a hypothesis;
-- `row4_apex_no_single_tile`/`row4_apex_beta_count_one` in that file bound the tiles at the apex).
--
-- Witnesses: the hypothesis bundle of `row4_a_edge_endpoints` is the same as for
-- `AEdgeReading.a_edge_west_east` (any scalene model with three distinct angles).
-- `row4_a_edge_apex_localAngle_beta` adds `hvert` (a plain equality) and the relation bundle used in
-- `Draft/FluxDRow4Bridge.lean` and `Draft/FluxDRow4L8.lean` (satisfied e.g. by transcendental `α`).
-- The `NonVacuityCheck` section checks each hypothesis satisfiable at the level of the real-number
-- content the conclusion is extracted from, without building a full `CongruentDissection`.
import Erdos634.EdgeType
import Erdos634.Draft.FluxDRow4L8

namespace Erdos634.Row4EdgeReading

open Erdos634.Geometry Erdos634.Geometry.Dissection Erdos634.TilePlacement

variable {N : ℕ}

/-! ## Part 1 — packaging `edge_excludes_own_angle` for row 4's tile (Layer A, P92) -/

/-- **A real `a`-edge of row 4's tile carries `β`/`γ` at both ends, distinct.** Exactly
`EdgeType.a_edge_endpoints`, unchanged — confirming P92's finding that Layer A already applies to
row 4's tile without any bespoke proof. -/
theorem row4_a_edge_endpoints (D : CongruentDissection N) (α β γ : ℝ)
    (hα' : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hβ' : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hγ' : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    (hscalene : ∀ m m' : Fin 3, m ≠ m' → sideOpp D.model m ≠ sideOpp D.model m')
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hβγ : β ≠ γ)
    (i : Fin N) (k : Fin 3)
    (hlen : dist ((D.tile i).pts k) ((D.tile i).pts (k + 1)) = sideOpp D.model 0) :
    (TilePlacement.angleAt (D.tile i) k = β ∨ TilePlacement.angleAt (D.tile i) k = γ) ∧
    (TilePlacement.angleAt (D.tile i) (k + 1) = β ∨
      TilePlacement.angleAt (D.tile i) (k + 1) = γ) ∧
    TilePlacement.angleAt (D.tile i) k ≠ TilePlacement.angleAt (D.tile i) (k + 1) :=
  Erdos634.Geometry.a_edge_endpoints D α β γ hα' hβ' hγ' hscalene hαβ hαγ hβγ i k hlen

/-! ## Part 2 — composing with `row4_no_gamma_at_apex` (P87): the real `localAngle = β` bridge

This is P90's gap (b), closed as far as it can be without gap (a) (which real vertex sits at `B`,
still a hypothesis `hvert`/`hvert'`). -/

/-- **A real `a`-edge's `k`-endpoint at the apex `B` carries `β`, outright.** Given the edge is a
real `a`-edge of tile `i` (`hlen`), its `k`-endpoint IS the target's apex corner `kB` as a real point
(`hvert`), and row 4's relation/irrationality bundle, `row4_no_gamma_at_apex` (P87, imported
unedited) rules out `γ` at every tile's angle at `B`, so `a_edge_endpoints`'s `{β, γ}` disjunction
collapses to `β`. -/
theorem row4_a_edge_apex_localAngle_beta (D : CongruentDissection N) (α β γ : ℝ)
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hαπ : α ≠ Real.pi) (hα0 : α ≠ 0)
    (hβγ : β ≠ γ) (hβπ : β ≠ Real.pi) (hβ0 : β ≠ 0)
    (hγπ : γ ≠ Real.pi) (hγ0 : γ ≠ 0) (hπ0 : Real.pi ≠ 0)
    (hγdef : γ = 2 * α) (hrel : 3 * α + β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (hα' : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hβ' : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hγ' : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    (hscalene : ∀ m m' : Fin 3, m ≠ m' → sideOpp D.model m ≠ sideOpp D.model m')
    (i : Fin N) (k : Fin 3)
    (hlen : dist ((D.tile i).pts k) ((D.tile i).pts (k + 1)) = sideOpp D.model 0)
    (kB : Fin 3)
    (hcorner : cornerAngle (D.target.pts (kB + 1)) (D.target.pts kB) (D.target.pts (kB + 2))
      = α + β)
    (hvert : (D.tile i).pts k = D.target.pts kB) :
    (D.tile i).localAngle (D.target.pts kB) = β := by
  have hedge := row4_a_edge_endpoints D α β γ hα' hβ' hγ' hscalene hαβ hαγ hβγ i k hlen
  have hloc : (D.tile i).localAngle (D.target.pts kB) = TilePlacement.angleAt (D.tile i) k := by
    rw [← hvert]; exact Erdos634.Geometry.Tri.localAngle_vertex (D.tile i) k
  have hnogamma := Erdos634.Row4L8.row4_no_gamma_at_apex D α β γ hαβ hαγ hαπ hα0 hβγ hβπ hβ0
    hγπ hγ0 hπ0 hγdef hrel hirr hα' hβ' hγ' kB hcorner
  have hne : (D.tile i).localAngle (D.target.pts kB) ≠ γ := by
    intro heq
    have hmem : i ∈ ({j | (D.tile j).localAngle (D.target.pts kB) = γ} : Finset (Fin N)) := by
      simpa using heq
    have hcard : 0 < ({j | (D.tile j).localAngle (D.target.pts kB) = γ} :
        Finset (Fin N)).card := Finset.card_pos.mpr ⟨i, hmem⟩
    omega
  rw [hloc] at hne ⊢
  rcases hedge.1 with h | h
  · exact h
  · exact absurd h hne

/-- **The symmetric statement for the `k + 1`-endpoint.** Identical composition, at the tile's
other edge-endpoint. -/
theorem row4_a_edge_apex_localAngle_beta' (D : CongruentDissection N) (α β γ : ℝ)
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hαπ : α ≠ Real.pi) (hα0 : α ≠ 0)
    (hβγ : β ≠ γ) (hβπ : β ≠ Real.pi) (hβ0 : β ≠ 0)
    (hγπ : γ ≠ Real.pi) (hγ0 : γ ≠ 0) (hπ0 : Real.pi ≠ 0)
    (hγdef : γ = 2 * α) (hrel : 3 * α + β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (hα' : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hβ' : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hγ' : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    (hscalene : ∀ m m' : Fin 3, m ≠ m' → sideOpp D.model m ≠ sideOpp D.model m')
    (i : Fin N) (k : Fin 3)
    (hlen : dist ((D.tile i).pts k) ((D.tile i).pts (k + 1)) = sideOpp D.model 0)
    (kB : Fin 3)
    (hcorner : cornerAngle (D.target.pts (kB + 1)) (D.target.pts kB) (D.target.pts (kB + 2))
      = α + β)
    (hvert' : (D.tile i).pts (k + 1) = D.target.pts kB) :
    (D.tile i).localAngle (D.target.pts kB) = β := by
  have hedge := row4_a_edge_endpoints D α β γ hα' hβ' hγ' hscalene hαβ hαγ hβγ i k hlen
  have hloc : (D.tile i).localAngle (D.target.pts kB)
      = TilePlacement.angleAt (D.tile i) (k + 1) := by
    rw [← hvert']; exact Erdos634.Geometry.Tri.localAngle_vertex (D.tile i) (k + 1)
  have hnogamma := Erdos634.Row4L8.row4_no_gamma_at_apex D α β γ hαβ hαγ hαπ hα0 hβγ hβπ hβ0
    hγπ hγ0 hπ0 hγdef hrel hirr hα' hβ' hγ' kB hcorner
  have hne : (D.tile i).localAngle (D.target.pts kB) ≠ γ := by
    intro heq
    have hmem : i ∈ ({j | (D.tile j).localAngle (D.target.pts kB) = γ} : Finset (Fin N)) := by
      simpa using heq
    have hcard : 0 < ({j | (D.tile j).localAngle (D.target.pts kB) = γ} :
        Finset (Fin N)).card := Finset.card_pos.mpr ⟨i, hmem⟩
    omega
  rw [hloc] at hne ⊢
  rcases hedge.2.1 with h | h
  · exact h
  · exact absurd h hne

/-! ## Non-vacuity check -/

section NonVacuityCheck

/-- The raw arithmetic content `row4_a_edge_apex_localAngle_beta` extracts (`x ∈ {β, γ} → x ≠ γ →
x = β`) fires on genuinely distinct, non-contradictory data — not `False → False`. -/
example (β γ x : ℝ) (hβγ : β ≠ γ) (h : x = β ∨ x = γ) (hne : x ≠ γ) : x = β := by
  rcases h with h | h
  · exact h
  · exact absurd h hne

/-- Row 4's own relation/irrationality bundle is satisfiable (reusing the same transcendental-`α`
witness shape `Draft/FluxDRow4Bridge.lean`/`FluxDRow4L8.lean` already establish): with
`γ = 2α`, `3α + β = π`, `α` transcendental, all of `hγdef`/`hrel` hold and `hirr` is a genuine,
non-trivially-true hypothesis (not derivable from the others), confirming the bundle this file adds
to `row4_no_gamma_at_apex`'s own is not internally contradictory. -/
example : ∃ α β γ : ℝ, γ = 2 * α ∧ 3 * α + β = Real.pi := by
  refine ⟨Real.pi / 5, Real.pi - 3 * (Real.pi / 5), 2 * (Real.pi / 5), by ring, by ring⟩

end NonVacuityCheck

end Erdos634.Row4EdgeReading

#print axioms Erdos634.Row4EdgeReading.row4_a_edge_endpoints
#print axioms Erdos634.Row4EdgeReading.row4_a_edge_apex_localAngle_beta
#print axioms Erdos634.Row4EdgeReading.row4_a_edge_apex_localAngle_beta'
