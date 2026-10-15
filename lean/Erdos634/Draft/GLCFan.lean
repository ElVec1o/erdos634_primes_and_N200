import Mathlib.Tactic
import Erdos634.Draft.G3GControl
import Erdos634.Draft.T30LPi3Tile
import Erdos634.Draft.FluxDRow4L8Recovered

/-!
# The angle fan at a boundary point, `γ = 2α` tile

`boundary_fan_2alpha`: for a `CongruentDissection` whose model has `TwoAlphaData α a b c` (angles `α, β = π−3α, γ = 2α`) with
`α ∉ ℚπ`, at a non-vertex point `v` of the target boundary the counts of tiles presenting `α, β, γ, π, 2π` are exactly one of
`(α,β,γ,π) = (0,0,0,1)`, `(3,1,0,0)` or `(1,1,1,0)`, never `2π`: so a vertex of the dissection on a side carries EXACTLY ONE `β`
and either `(α,γ)` or `(α,α,α)`; a point with no tile vertex has a single straight tile.
Built from `Row4.count_eq` and `Row4.fig_arith`; the new content is the full case list, with the counts named.

Witness `witness_fan`: the real certified 1125-tiling `G3GControl.D` (tile `(4,5,6)·16`, `k = 2`) at the midpoint of the base.
Counterexample `fan_needs_irr`: with `α = π/5` (rational) the equation `5α = π` has the spurious solution `(5,0,0,0)`.
-/

namespace Erdos634.GLC

open Erdos634.Geometry

variable {N : ℕ}

/-- Number of tiles presenting angle `θ` at `v`. -/
noncomputable def cntA (D : CongruentDissection N) (v : Plane) (θ : ℝ) : ℕ :=
  ({i | (D.tile i).localAngle v = θ} : Finset (Fin N)).card

/-- **Boundary fan (lemma (1)).** -/
theorem boundary_fan_2alpha (D : CongruentDissection N) {α a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (h : D.model.TwoAlphaData α a b c)
    {v : Plane} (hv : v ∈ frontier D.target.carrier) (hnv : v ∉ Set.range D.target.pts) :
    cntA D v (2 * Real.pi) = 0 ∧
    ((cntA D v α = 0 ∧ cntA D v (Real.pi - 3 * α) = 0 ∧ cntA D v (2 * α) = 0 ∧ cntA D v Real.pi = 1) ∨
     (cntA D v α = 3 ∧ cntA D v (Real.pi - 3 * α) = 1 ∧ cntA D v (2 * α) = 0 ∧ cntA D v Real.pi = 0) ∨
     (cntA D v α = 1 ∧ cntA D v (Real.pi - 3 * α) = 1 ∧ cntA D v (2 * α) = 1 ∧ cntA D v Real.pi = 0)) := by
  obtain ⟨hα0, hα3, -⟩ := Row4.model_sides D h
  have hc := Row4.count_eq D hα h hα0 hα3 v
  rw [D.target.localAngle_frontier hv hnv] at hc
  unfold cntA
  set P₁ := ({i | (D.tile i).localAngle v = α} : Finset (Fin N)).card
  set Q₁ := ({i | (D.tile i).localAngle v = Real.pi - 3 * α} : Finset (Fin N)).card
  set R₁ := ({i | (D.tile i).localAngle v = 2 * α} : Finset (Fin N)).card
  set S₁ := ({i | (D.tile i).localAngle v = Real.pi} : Finset (Fin N)).card
  set T₁ := ({i | (D.tile i).localAngle v = 2 * Real.pi} : Finset (Fin N)).card
  obtain ⟨h1, h2⟩ := Row4.fig_arith hα (P := P₁) (Q := Q₁) (R := R₁) (S := S₁) (T := T₁)
    (j := 1) (k := 0) (by push_cast; linear_combination -hc)
  omega

/-- A vertex of the dissection on the side (a point where some tile has a corner) carries exactly one `β`:
the case `S₁ = 0`. -/
theorem fan_one_beta (D : CongruentDissection N) {α a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (h : D.model.TwoAlphaData α a b c)
    {v : Plane} (hv : v ∈ frontier D.target.carrier) (hnv : v ∉ Set.range D.target.pts)
    (hcorner : ∃ i, ∃ j : Fin 3, (D.tile i).pts j = v) :
    cntA D v (Real.pi - 3 * α) = 1 ∧
    ((cntA D v α = 3 ∧ cntA D v (2 * α) = 0) ∨ (cntA D v α = 1 ∧ cntA D v (2 * α) = 1)) := by
  obtain ⟨-, hf⟩ := boundary_fan_2alpha D hα h hv hnv
  rcases hf with ⟨h1, h2, h3, h4⟩ | hf | hf
  · exfalso
    obtain ⟨i, j, hij⟩ := hcorner
    have hloc : (D.tile i).localAngle v = (D.tile i).angleAt j := by
      rw [← hij]; exact Tri.localAngle_vertex _ _
    have hp : (D.tile i).localAngle v ≠ 0 := by
      rw [hloc]; exact (D.tile i).angleAt_pos' j |>.ne'
    have hmem := Row4.localAngle_mem D h v i
    have hang := Row4.tile_angle_mem D h i j
    have hcards : ∀ θ, (D.tile i).localAngle v = θ → 0 < cntA D v θ := fun θ hθ =>
      Finset.card_pos.mpr ⟨i, by simp [hθ]⟩
    rcases hang with e | e | e
    · have := hcards α (hloc.trans e); omega
    · have := hcards _ (hloc.trans e); omega
    · have := hcards _ (hloc.trans e); omega
  · exact ⟨hf.2.1, Or.inl ⟨hf.1, hf.2.2.1⟩⟩
  · exact ⟨hf.2.1, Or.inr ⟨hf.1, hf.2.2.1⟩⟩

/-- At most one `β` and at most one `γ` at such a point: two distinct tiles never present the same `β` or `γ`. -/
theorem angles_differ_2alpha (D : CongruentDissection N) {α a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (h : D.model.TwoAlphaData α a b c)
    {v : Plane} (hv : v ∈ frontier D.target.carrier) (hnv : v ∉ Set.range D.target.pts)
    {i j : Fin N} (hij : i ≠ j)
    (hi : (D.tile i).localAngle v = Real.pi - 3 * α ∨ (D.tile i).localAngle v = 2 * α) :
    (D.tile i).localAngle v ≠ (D.tile j).localAngle v := by
  intro heq
  obtain ⟨-, hf⟩ := boundary_fan_2alpha D hα h hv hnv
  have key : ∀ θ : ℝ, (D.tile i).localAngle v = θ → (D.tile j).localAngle v = θ → 2 ≤ cntA D v θ := by
    intro θ hθi hθj
    unfold cntA
    have : 1 < ({i | (D.tile i).localAngle v = θ} : Finset (Fin N)).card :=
      Finset.one_lt_card.mpr ⟨i, by simp [hθi], j, by simp [hθj], hij⟩
    omega
  rcases hi with hi | hi
  · have := key _ hi (heq ▸ hi); rcases hf with ⟨-, h2, -⟩ | ⟨-, h2, -⟩ | ⟨-, h2, -⟩ <;> omega
  · have := key _ hi (heq ▸ hi); rcases hf with ⟨-, -, h2, -⟩ | ⟨-, -, h2, -⟩ | ⟨-, -, h2, -⟩ <;> omega

/-- If `α` were rational (`π/5`, then `γ = β = 2π/5`) the fan equation has the spurious solution
five `α`'s: the conclusion `Q + S + 2T = 1` of `Row4.fig_arith` fails. -/
theorem fan_needs_irr :
    ((5 : ℕ) : ℝ) * (Real.pi / 5) + ((0 : ℕ) : ℝ) * (Real.pi - 3 * (Real.pi / 5))
      + ((0 : ℕ) : ℝ) * (2 * (Real.pi / 5)) + ((0 : ℕ) : ℝ) * Real.pi + ((0 : ℕ) : ℝ) * (2 * Real.pi)
      = ((1 : ℤ) : ℝ) * Real.pi + ((0 : ℤ) : ℝ) * (Real.pi / 5) ∧
    ¬ ((0 : ℤ) + 0 + 2 * 0 = 1) ∧ ∃ r : ℚ, Real.pi / 5 = (r : ℝ) * Real.pi := by
  refine ⟨by push_cast; ring, by decide, 1 / 5, by push_cast; ring⟩

/-! ## Witness: the real 1125-tiling -/

open Erdos634.Draft.G3GControl in
/-- the boundary non-vertex point used by the witness: midpoint of the edge `0→1` of the target. -/
noncomputable def wpt : Plane := midpoint ℝ (D.target.pts 0) (D.target.pts (0 + 1))

open Erdos634.Draft.G3GControl in
/-- every hypothesis discharged on the real `N = 1125` dissection at a boundary non-vertex point. -/
theorem witness_fan :
    cntA D wpt (2 * Real.pi) = 0 ∧
    ((cntA D wpt α = 0 ∧ cntA D wpt (Real.pi - 3 * α) = 0 ∧ cntA D wpt (2 * α) = 0 ∧ cntA D wpt Real.pi = 1) ∨
     (cntA D wpt α = 3 ∧ cntA D wpt (Real.pi - 3 * α) = 1 ∧ cntA D wpt (2 * α) = 0 ∧ cntA D wpt Real.pi = 0) ∨
     (cntA D wpt α = 1 ∧ cntA D wpt (Real.pi - 3 * α) = 1 ∧ cntA D wpt (2 * α) = 1 ∧ cntA D wpt Real.pi = 0)) := by
  obtain ⟨hf, hn⟩ := Erdos634.Pi3Tile.edge_mid D.target 0
  exact boundary_fan_2alpha D α_irr data hf hn

end Erdos634.GLC

#print axioms Erdos634.GLC.boundary_fan_2alpha
#print axioms Erdos634.GLC.fan_one_beta
#print axioms Erdos634.GLC.angles_differ_2alpha
#print axioms Erdos634.GLC.witness_fan
