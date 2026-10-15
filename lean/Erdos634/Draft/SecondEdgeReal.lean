-- The two geometric hypotheses of `SecondEdge.admissible_ends_alpha`,
-- proved for a real `CongruentDissection`.
--
-- `SecondEdge.admissible_ends_alpha` (Walls13/SecondEdge.lean) proves by exhaustion that every
-- admissible angular ordering at junction J ends in α.  Its two hypotheses are:
--   (H1) The vertex figure at J is one of the two straight figures {3α,2β} or {α,β,γ}.
--   (H2) T₁ (the apex c-edge's tile) presents β at J.
--
-- This file proves H1 and H2 for a real `CongruentDissection`.  It does not prove the cyclic ordering
-- of tiles at J (which tile is "last" against the descending side); connecting the real cyclic order
-- to the abstract list is a separate step.

import Erdos634.EdgeType
import Erdos634.TileAt
import Erdos634.SideWall

open scoped Classical

namespace Erdos634.SecondEdgeReal

open Erdos634.Geometry Erdos634.Geometry.Dissection Erdos634.Placement Erdos634.TilePlacement

variable {N : ℕ}

/-! ## H2: the apex c-tile presents β at J -/

/-- **H2: the apex c-tile presents β at J.**
Given a wall edge `p` where:
  - `p` is a c-edge (dist between its endpoints = sideOpp D.model 2),
  - the east endpoint of `p` equals the apex corner (angle 3α),
the tile `D.tile p.1` presents β at the west endpoint J = edgeWest p.

Proof chain:
  1. `c_edge_endpoints`: {angleAt p.2, angleAt (p.2+1)} = {α,β} (not γ, distinct).
  2. `congruentDissection_apex_counts`: β count at the apex = 0.
  3. `localAngle_edgeWest_edgeEast`: T₁'s local angle at edgeEast = angleAt at one index.
  4. Since edgeEast = apex, that angleAt ≠ β (step 2), hence = α (from step 1).
  5. The other angleAt (at edgeWest = J) is the remaining value = β. -/
theorem apex_c_tile_presents_beta (D : CongruentDissection N) (α β γ : ℝ)
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hαπ : α ≠ Real.pi) (hα0 : α ≠ 0)
    (hβγ : β ≠ γ) (hβπ : β ≠ Real.pi) (hβ0 : β ≠ 0)
    (hγπ : γ ≠ Real.pi) (hγ0 : γ ≠ 0) (hπ0 : Real.pi ≠ 0)
    (hγdef : γ = 2 * α + β) (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (hα' : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hβ' : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hγ' : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    (hscalene : ∀ m m' : Fin 3, m ≠ m' → sideOpp D.model m ≠ sideOpp D.model m')
    (dir : Plane →ₗ[ℝ] ℝ) (p : Fin N × Fin 3)
    (hc : dist ((D.tile p.1).pts p.2) ((D.tile p.1).pts (p.2 + 1)) = sideOpp D.model 2)
    (kapex : Fin 3)
    (hcornerapex : cornerAngle (D.target.pts (kapex + 1)) (D.target.pts kapex)
      (D.target.pts (kapex + 2)) = 3 * α)
    (heast : edgeEast D.toDissection dir p = D.target.pts kapex) :
    (D.tile p.1).localAngle (edgeWest D.toDissection dir p) = β := by
  obtain ⟨hk_ab, hk1_ab, hne⟩ :=
    c_edge_endpoints D α β γ hα' hβ' hγ' hscalene hαβ hαγ hβγ p.1 p.2 hc
  have hapex_counts := congruentDissection_apex_counts D α β γ
    hαβ hαγ hαπ hα0 hβγ hβπ hβ0 hγπ hγ0 hπ0 hγdef hrel hirr hα' hβ' hγ' kapex hcornerapex
  -- No tile presents β at the apex: the β-count finset has card 0
  have hno_beta_apex : (D.tile p.1).localAngle (D.target.pts kapex) ≠ β := by
    intro h
    have hmem : p.1 ∈ ({i | (D.tile i).localAngle (D.target.pts kapex) = β} : Finset (Fin N)) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact h
    simp [Finset.card_eq_zero.mp hapex_counts.2.1] at hmem
  rcases Erdos634.Geometry.localAngle_edgeWest_edgeEast D.toDissection dir p.1 p.2 with
    ⟨hw, he⟩ | ⟨hw, he⟩
  · -- west = angleAt p.2, east = angleAt (p.2+1)
    rw [← heast] at hno_beta_apex; rw [he] at hno_beta_apex
    have hk1_alpha : angleAt (D.tile p.1) (p.2 + 1) = α := hk1_ab.resolve_right hno_beta_apex
    have hk_beta : angleAt (D.tile p.1) p.2 = β :=
      hk_ab.resolve_left (fun h => hne (h.trans hk1_alpha.symm))
    rw [hw, hk_beta]
  · -- west = angleAt (p.2+1), east = angleAt p.2
    rw [← heast] at hno_beta_apex; rw [he] at hno_beta_apex
    have hk_alpha : angleAt (D.tile p.1) p.2 = α := hk_ab.resolve_right hno_beta_apex
    have hk1_beta : angleAt (D.tile p.1) (p.2 + 1) = β :=
      hk1_ab.resolve_left (fun h => hne.symm (h.trans hk_alpha.symm))
    rw [hw, hk1_beta]

/-! ## H1: The vertex figure at J is straight -/

/-- **H1: The vertex figure at J is {3α,2β} or {α,β,γ}.**
Given a boundary non-vertex J at which some tile presents β ≠ π (specifically T₁ from H2),
the three-case classification reduces to the two straight-figure cases. -/
theorem junction_straight_figure (D : CongruentDissection N) (α β γ : ℝ)
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hαπ : α ≠ Real.pi) (hα0 : α ≠ 0)
    (hβγ : β ≠ γ) (hβπ : β ≠ Real.pi) (hβ0 : β ≠ 0)
    (hγπ : γ ≠ Real.pi) (hγ0 : γ ≠ 0) (hπ0 : Real.pi ≠ 0)
    (hγdef : γ = 2 * α + β) (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (hα' : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hβ' : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hγ' : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    {J : Plane}
    (hJ_frontier : J ∈ frontier D.target.carrier)
    (hJ_nonvertex : J ∉ Set.range D.target.pts)
    (i₁ : Fin N) (hbeta : (D.tile i₁).localAngle J = β) :
    (({i | (D.tile i).localAngle J = α} : Finset (Fin N)).card = 3 ∧
      ({i | (D.tile i).localAngle J = β} : Finset (Fin N)).card = 2 ∧
      ({i | (D.tile i).localAngle J = γ} : Finset (Fin N)).card = 0) ∨
    (({i | (D.tile i).localAngle J = α} : Finset (Fin N)).card = 1 ∧
      ({i | (D.tile i).localAngle J = β} : Finset (Fin N)).card = 1 ∧
      ({i | (D.tile i).localAngle J = γ} : Finset (Fin N)).card = 1) :=
  congruentDissection_boundary_figure_cases_at_vertex D α β γ
    hαβ hαγ hαπ hα0 hβγ hβπ hβ0 hγπ hγ0 hπ0 hγdef hrel hirr hα' hβ' hγ'
    hJ_frontier hJ_nonvertex i₁ (Or.inr (Or.inl hbeta))

end Erdos634.SecondEdgeReal
