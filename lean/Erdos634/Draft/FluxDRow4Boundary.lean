-- Draft/FluxDRow4Boundary.lean: the boundary-figure classification for the `γ = 2α` tile: at most
-- one γ-tile touches any boundary point of a target side (`g2a_vertex_multiplicities`,
-- `g2a_side_figure`).
--
-- `TileAt.congruentDissection_boundary_figure_cases` proves the analogous fact for the base-β tile
-- (relation `γ = 2α + β`, `3α + 2β = π`).  The tile here has the relation `γ = 2α`, `3α + β = π`
-- (angles as in `Draft/FluxRow4.lean`, used by `Draft/FluxDRow4Bridge.lean`).  The method is the
-- same (`TileAt.lean`, `VertexFigureReal.lean` for the arithmetic core):
--   1. Arithmetic (`boundary_figure_row4`/`boundary_figure_cases_row4`): substitute `γ = 2α`,
--      `β = π − 3α` into `p·α + q·β + r·γ + s·π = π` (one substitution, not two), and close by
--      `Geometry.angle_indep`.  The solutions are `p + 2r = 3q`, `q + s = 1`,
--      `(p,q,r,s) ∈ {(0,0,0,1),(3,1,0,0),(1,1,1,0)}`.
--   2. Dissection-level counts (`row4_boundary_figure_cases`): compose step 1 with
--      `VertexFigureReal.boundary_multiplicities_cards`, which is independent of the tile relation
--      (it needs only the five-value membership `hvals` and pairwise distinctness of
--      `α, β, γ, π, 0`).
--   3. `CongruentDissection`-level statement (`congruentDissection_row4_boundary_figure_cases`):
--      compose step 2 with `TileAt.congruentDissection_localAngle_mem_boundary`, also independent of
--      the tile relation.
--   4. `congruentDissection_row4_boundary_gamma_le_one`: at most one γ-tile at any boundary point,
--      read off the `r`-values of the three cases (`0, 0, 1`, never `2`).
--
-- Non-vacuity: the ambient hypothesis `α ∉ ℚπ` is satisfiable (e.g. any transcendental `α`), and
-- `hα'`/`hβ'`/`hγ'`/`hv`/`hnv` are the same shape of hypothesis that
-- `TileAt.congruentDissection_boundary_figure_cases` carries for the base-β family.
--
-- Not covered: the application of this fact along a leg (`Draft/FluxDRow4L8.lean`), the `{a,c}`-leg
-- case (a different argument without angle-multiset content), and the word-level statements
-- (`hword`, `not_prime`).
import Erdos634.TileAt
import Erdos634.Draft.FluxDRow4Bridge

namespace Erdos634.Row4Boundary

open Erdos634.Geometry Erdos634.Geometry.Dissection

variable {N : ℕ}

/-! ## Step 1 — the arithmetic core, row 4's relation -/

/-- **Row 4's boundary-figure arithmetic.** From `p·α + q·β + r·γ + s·π = π` with `γ = 2α`,
`3α + β = π` and `α ∉ ℚπ`. The row-4 analogue of `VertexFigureReal.boundary_figure` (base-β's
`γ = 2α + β`, `3α + 2β = π`) — one substitution instead of two, since `γ` here is a pure multiple
of `α`. -/
theorem boundary_figure_row4 {α β γ : ℝ} (hγ : γ = 2 * α) (hrel : 3 * α + β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (p q r s : ℕ)
    (hsum : (p : ℝ) * α + (q : ℝ) * β + (r : ℝ) * γ + (s : ℝ) * Real.pi = Real.pi) :
    ((p : ℤ) + 2 * r = 3 * q ∧ (q : ℤ) + s = 1) := by
  have hβ : β = Real.pi - 3 * α := by linarith
  have hkey : (((p : ℤ) + 2 * r - 3 * q : ℤ) : ℝ) * α
      + (((q : ℤ) + s - 1 : ℤ) : ℝ) * Real.pi = 0 := by
    rw [hγ, hβ] at hsum
    push_cast
    linarith [hsum]
  obtain ⟨hA, hB⟩ := Erdos634.Geometry.angle_indep hirr _ _ hkey
  refine ⟨by omega, by omega⟩

/-- **The three row-4 boundary figures.** Solving `p + 2r = 3q`, `q + s = 1` over `ℕ`: either
`q = 0` (forcing `p = r = 0`, `s = 1`, the single-straight-angle case), or `q = 1` (forcing `s = 0`
and `(p, r) ∈ {(3, 0), (1, 1)}`). In particular `r ≤ 1` always — `r = 2` never occurs, which is
exactly the fact L8 needs. -/
theorem boundary_figure_cases_row4 {α β γ : ℝ} (hγ : γ = 2 * α) (hrel : 3 * α + β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (p q r s : ℕ)
    (hsum : (p : ℝ) * α + (q : ℝ) * β + (r : ℝ) * γ + (s : ℝ) * Real.pi = Real.pi) :
    (s = 1 ∧ p = 0 ∧ q = 0 ∧ r = 0) ∨
      (s = 0 ∧ ((p = 3 ∧ q = 1 ∧ r = 0) ∨ (p = 1 ∧ q = 1 ∧ r = 1))) := by
  obtain ⟨h1, h2⟩ := boundary_figure_row4 hγ hrel hirr p q r s hsum
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · left; refine ⟨by omega, by omega, rfl, by omega⟩
  · have hq1 : q = 1 := by omega
    subst hq1
    right
    refine ⟨by omega, ?_⟩
    omega

/-- **At most one `γ`-tile's worth of multiplicity, arithmetically.** The direct corollary of
`boundary_figure_cases_row4` that L8's `b^k`-leg step needs: `r` (the `γ`-multiplicity) is never
more than `1`. -/
theorem boundary_gamma_le_one_row4 {α β γ : ℝ} (hγ : γ = 2 * α) (hrel : 3 * α + β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (p q r s : ℕ)
    (hsum : (p : ℝ) * α + (q : ℝ) * β + (r : ℝ) * γ + (s : ℝ) * Real.pi = Real.pi) :
    r ≤ 1 := by
  rcases boundary_figure_cases_row4 hγ hrel hirr p q r s hsum with
    ⟨-, -, -, hr⟩ | ⟨-, ⟨-, -, hr⟩ | ⟨-, -, hr⟩⟩ <;> omega

/-! ## Step 2 — Dissection-level counts

`VertexFigureReal.boundary_multiplicities_cards` is already tile-relation-agnostic: it only needs
the five-value membership `hvals` and pairwise distinctness of `α, β, γ, π, 0`, never `hγdef`/
`hrel`. Reused verbatim, not redefined. -/

open Erdos634.VertexFigureReal in
/-- **Row 4's boundary figure, with the counts named (`Dissection`-level).** -/
theorem row4_boundary_figure_cases {N : ℕ} (D : Dissection N) (α β γ : ℝ)
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hαπ : α ≠ Real.pi) (hα0 : α ≠ 0)
    (hβγ : β ≠ γ) (hβπ : β ≠ Real.pi) (hβ0 : β ≠ 0)
    (hγπ : γ ≠ Real.pi) (hγ0 : γ ≠ 0) (hπ0 : Real.pi ≠ 0)
    (hγdef : γ = 2 * α) (hrel : 3 * α + β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    {v : Plane} (hv : v ∈ frontier D.target.carrier) (hnv : v ∉ Set.range D.target.pts)
    (hvals : ∀ i, (D.tile i).localAngle v ∈ ({α, β, γ, Real.pi, 0} : Finset ℝ)) :
    (({i | (D.tile i).localAngle v = Real.pi} : Finset (Fin N)).card = 1 ∧
      ({i | (D.tile i).localAngle v = α} : Finset (Fin N)).card = 0 ∧
      ({i | (D.tile i).localAngle v = β} : Finset (Fin N)).card = 0 ∧
      ({i | (D.tile i).localAngle v = γ} : Finset (Fin N)).card = 0) ∨
    (({i | (D.tile i).localAngle v = α} : Finset (Fin N)).card = 3 ∧
      ({i | (D.tile i).localAngle v = β} : Finset (Fin N)).card = 1 ∧
      ({i | (D.tile i).localAngle v = γ} : Finset (Fin N)).card = 0) ∨
    (({i | (D.tile i).localAngle v = α} : Finset (Fin N)).card = 1 ∧
      ({i | (D.tile i).localAngle v = β} : Finset (Fin N)).card = 1 ∧
      ({i | (D.tile i).localAngle v = γ} : Finset (Fin N)).card = 1) := by
  have hsum := boundary_multiplicities_cards D α β γ hαβ hαγ hαπ hα0 hβγ hβπ hβ0
    hγπ hγ0 hπ0 hv hnv hvals
  rcases boundary_figure_cases_row4 hγdef hrel hirr _ _ _ _ hsum with
    ⟨hs, hp, hq, hr⟩ | ⟨hs, hcase⟩
  · exact Or.inl ⟨hs, hp, hq, hr⟩
  · rcases hcase with ⟨hp, hq, hr⟩ | ⟨hp, hq, hr⟩
    · exact Or.inr (Or.inl ⟨hp, hq, hr⟩)
    · exact Or.inr (Or.inr ⟨hp, hq, hr⟩)

/-- **At most one `γ`-tile at a boundary point (`Dissection`-level).** -/
theorem row4_boundary_gamma_le_one {N : ℕ} (D : Dissection N) (α β γ : ℝ)
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hαπ : α ≠ Real.pi) (hα0 : α ≠ 0)
    (hβγ : β ≠ γ) (hβπ : β ≠ Real.pi) (hβ0 : β ≠ 0)
    (hγπ : γ ≠ Real.pi) (hγ0 : γ ≠ 0) (hπ0 : Real.pi ≠ 0)
    (hγdef : γ = 2 * α) (hrel : 3 * α + β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    {v : Plane} (hv : v ∈ frontier D.target.carrier) (hnv : v ∉ Set.range D.target.pts)
    (hvals : ∀ i, (D.tile i).localAngle v ∈ ({α, β, γ, Real.pi, 0} : Finset ℝ)) :
    ({i | (D.tile i).localAngle v = γ} : Finset (Fin N)).card ≤ 1 := by
  rcases row4_boundary_figure_cases D α β γ hαβ hαγ hαπ hα0 hβγ hβπ hβ0 hγπ hγ0 hπ0
    hγdef hrel hirr hv hnv hvals with ⟨-, -, -, hr⟩ | ⟨-, -, hr⟩ | ⟨-, -, hr⟩ <;> omega

/-! ## Step 3 — `CongruentDissection`-level, row 4's analogue of
`TileAt.congruentDissection_boundary_figure_cases`

`TileAt.congruentDissection_localAngle_mem_boundary` is already fully relation-agnostic (it only
names the model's three corner angles via `hα'`/`hβ'`/`hγ'`, and never mentions `hγdef`/`hrel`).
Reused verbatim, not redefined. -/


/-- **Row 4's boundary figure, classified — for a real `CongruentDissection`.** The row-4 analogue
of `TileAt.congruentDissection_boundary_figure_cases`. At any point of the target's frontier that
is not a target vertex, the tiles covering it are either a single tile presenting a straight angle,
or exactly `{3α, β}`, or exactly `{α, β, γ}`. -/
theorem congruentDissection_row4_boundary_figure_cases (D : CongruentDissection N) (α β γ : ℝ)
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hαπ : α ≠ Real.pi) (hα0 : α ≠ 0)
    (hβγ : β ≠ γ) (hβπ : β ≠ Real.pi) (hβ0 : β ≠ 0)
    (hγπ : γ ≠ Real.pi) (hγ0 : γ ≠ 0) (hπ0 : Real.pi ≠ 0)
    (hγdef : γ = 2 * α) (hrel : 3 * α + β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (hα' : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hβ' : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hγ' : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    {v : Plane} (hv : v ∈ frontier D.target.carrier) (hnv : v ∉ Set.range D.target.pts) :
    (({i | (D.tile i).localAngle v = Real.pi} : Finset (Fin N)).card = 1 ∧
      ({i | (D.tile i).localAngle v = α} : Finset (Fin N)).card = 0 ∧
      ({i | (D.tile i).localAngle v = β} : Finset (Fin N)).card = 0 ∧
      ({i | (D.tile i).localAngle v = γ} : Finset (Fin N)).card = 0) ∨
    (({i | (D.tile i).localAngle v = α} : Finset (Fin N)).card = 3 ∧
      ({i | (D.tile i).localAngle v = β} : Finset (Fin N)).card = 1 ∧
      ({i | (D.tile i).localAngle v = γ} : Finset (Fin N)).card = 0) ∨
    (({i | (D.tile i).localAngle v = α} : Finset (Fin N)).card = 1 ∧
      ({i | (D.tile i).localAngle v = β} : Finset (Fin N)).card = 1 ∧
      ({i | (D.tile i).localAngle v = γ} : Finset (Fin N)).card = 1) := by
  have hvals := congruentDissection_localAngle_mem_boundary D α β γ hα' hβ' hγ' hv hnv
  exact row4_boundary_figure_cases D.toDissection α β γ hαβ hαγ hαπ hα0 hβγ hβπ hβ0
    hγπ hγ0 hπ0 hγdef hrel hirr hv hnv hvals

/-! ## Step 4 — L8's actual needed fact -/


/-- **L8's needed fact, for a real `CongruentDissection`.** At most one `γ`-tile of row 4's family
touches any boundary point of a target side that is not a target vertex — exactly what L8's
`b^k`-leg step needs. -/
theorem congruentDissection_row4_boundary_gamma_le_one (D : CongruentDissection N) (α β γ : ℝ)
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hαπ : α ≠ Real.pi) (hα0 : α ≠ 0)
    (hβγ : β ≠ γ) (hβπ : β ≠ Real.pi) (hβ0 : β ≠ 0)
    (hγπ : γ ≠ Real.pi) (hγ0 : γ ≠ 0) (hπ0 : Real.pi ≠ 0)
    (hγdef : γ = 2 * α) (hrel : 3 * α + β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (hα' : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hβ' : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hγ' : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    {v : Plane} (hv : v ∈ frontier D.target.carrier) (hnv : v ∉ Set.range D.target.pts) :
    ({i | (D.tile i).localAngle v = γ} : Finset (Fin N)).card ≤ 1 := by
  rcases congruentDissection_row4_boundary_figure_cases D α β γ hαβ hαγ hαπ hα0 hβγ hβπ hβ0
    hγπ hγ0 hπ0 hγdef hrel hirr hα' hβ' hγ' hv hnv with ⟨-, -, -, hr⟩ | ⟨-, -, hr⟩ | ⟨-, -, hr⟩ <;>
    omega

end Erdos634.Row4Boundary

#print axioms Erdos634.Row4Boundary.boundary_figure_row4
#print axioms Erdos634.Row4Boundary.boundary_figure_cases_row4
#print axioms Erdos634.Row4Boundary.boundary_gamma_le_one_row4
#print axioms Erdos634.Row4Boundary.row4_boundary_figure_cases
#print axioms Erdos634.Row4Boundary.row4_boundary_gamma_le_one
#print axioms Erdos634.Row4Boundary.congruentDissection_row4_boundary_figure_cases
#print axioms Erdos634.Row4Boundary.congruentDissection_row4_boundary_gamma_le_one
