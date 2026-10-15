-- Draft/LemCensusFormal.lean — the vertex census, as ONE statement.
-- For a dissection of the base-β target (isosceles, base angles β, apex the remaining corner) by the
-- tile (α,β,γ=2α+β), 3α+2β=π, α∉ℚπ: every tile vertex carries one of the eight listed figures; the
-- base corners fill uniquely as {β} and the apex as {3α}; and v₁ = 1 + n₂ + v₃ + 2 v₄, in particular
-- v₁ ≥ 1.  Assembled from existing theorems (`figureVec_mem_censusLabels`,
-- `TileAt.congruentDissection_{apex,base_corner}_counts`, `congruentDissection_vertex_census_isosceles`).
-- `census_equations_equiv`: the three balance equations are exactly
-- one relation (rank 2), the entire content of corner counting.
import Erdos634.CornerAnglePermTarget
import Erdos634.CornerAnglePermCensus
import Erdos634.MarchKillsFan
import Erdos634.MarchSlots
import Erdos634.TileAt

open scoped Classical

namespace Erdos634.Draft.LemCensusFormal

open Erdos634.Geometry

/-- The `(α, β, γ)`-multiplicity vector at a point: the class label of the census. -/
noncomputable def fig {N : ℕ} (D : CongruentDissection N) (α β γ : ℝ) (v : Plane) : ℕ × ℕ × ℕ :=
  (({i | (D.tile i).localAngle v = α} : Finset (Fin N)).card,
   ({i | (D.tile i).localAngle v = β} : Finset (Fin N)).card,
   ({i | (D.tile i).localAngle v = γ} : Finset (Fin N)).card)

/-- The number of tile vertices carrying the figure `x`. -/
noncomputable def cnt {N : ℕ} (D : CongruentDissection N) (α β γ : ℝ) (x : ℕ × ℕ × ℕ) : ℕ :=
  ((cornerPts D.toDissection).filter (fun v => fig D α β γ v = x)).card

/-- **The vertex census**: classification of the figures, unique corner fills, the identity
`v₁ = 1 + n₂ + v₃ + 2v₄` (with `v₁ = #{β,3γ}`, `n₂ = #{3α,2β}`, `v₃ = #{4α,3β,γ}`, `v₄ = #{6α,4β}`)
and `v₁ ≥ 1`.  `a` is the apex index of the isosceles target (the other two corners are `β`). -/
theorem lem_census_exact {N : ℕ} (D : CongruentDissection N) {α β γ : ℝ}
    (hA : Erdos634.MarchSlots.AngleData α β γ)
    (hmα : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hmβ : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hmγ : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    (a : Fin 3)
    (hb₁ : cornerAngle (D.target.pts (a + 1 + 1)) (D.target.pts (a + 1))
      (D.target.pts (a + 1 + 2)) = β)
    (hb₂ : cornerAngle (D.target.pts (a + 2 + 1)) (D.target.pts (a + 2))
      (D.target.pts (a + 2 + 2)) = β) :
    (∀ v ∈ cornerPts D.toDissection, fig D α β γ v ∈ censusLabels) ∧
    fig D α β γ (D.target.pts a) = (3, 0, 0) ∧
    fig D α β γ (D.target.pts (a + 1)) = (0, 1, 0) ∧
    fig D α β γ (D.target.pts (a + 2)) = (0, 1, 0) ∧
    cnt D α β γ (0, 1, 3) = 1 + cnt D α β γ (3, 2, 0) + cnt D α β γ (4, 3, 1)
      + 2 * cnt D α β γ (6, 4, 0) ∧
    1 ≤ cnt D α β γ (0, 1, 3) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ :=
    MarchKillsFan.distinct_of_pos_ne hA.hα hA.hβ hA.hαβ hA.hγdef hA.hrel
  have hpi := Real.pi_pos
  have hα2π : α ≠ 2 * Real.pi := by
    intro h; have := hA.hrel; have := hA.hβ; linarith
  have hβ2π : β ≠ 2 * Real.pi := by
    intro h; have := hA.hrel; have := hA.hα; linarith
  have hγ2π : γ ≠ 2 * Real.pi := by
    intro h; have := hA.hγdef; have := hA.hrel; have := hA.hα; have := hA.hβ; linarith
  have hπ2π : Real.pi ≠ 2 * Real.pi := by intro h; linarith
  have h2π0 : 2 * Real.pi ≠ 0 := by positivity
  have hcls := fun {v : Plane} (hv : v ∈ cornerPts D.toDissection) =>
    figureVec_mem_censusLabels D α β γ h1 h2 h3 hα2π h4 h5 h6 hβ2π h7 h8 hγ2π h9 hπ2π h10 h2π0
      hmα hmβ hmγ hA.hγdef hA.hrel hA.hirr
      (htarget_of_isosceles D.target hA.hrel a hb₁ hb₂) hv
  obtain ⟨ap1, ap2, ap3, -⟩ := Dissection.congruentDissection_apex_counts D α β γ h1 h2 h3 h4 h5
    h6 h7 h8 h9 h10 hA.hγdef hA.hrel hA.hirr hmα hmβ hmγ a
    (target_apex_angle D.target hA.hrel a hb₁ hb₂)
  obtain ⟨b11, b12, b13, -⟩ := Dissection.congruentDissection_base_corner_counts D α β γ h1 h2 h3
    h4 h5 h6 h7 h8 h9 h10 hA.hγdef hA.hrel hA.hirr hmα hmβ hmγ (a + 1) hb₁
  obtain ⟨b21, b22, b23, -⟩ := Dissection.congruentDissection_base_corner_counts D α β γ h1 h2 h3
    h4 h5 h6 h7 h8 h9 h10 hA.hγdef hA.hrel hA.hirr hmα hmβ hmγ (a + 2) hb₂
  have hid := congruentDissection_vertex_census_isosceles D α β γ h1 h2 h3 hα2π h4 h5 h6 hβ2π h7
    h8 hγ2π h9 hπ2π h10 h2π0 hmα hmβ hmγ hA.hγdef hA.hrel hA.hirr a hb₁ hb₂
  refine ⟨fun v hv => hcls hv, ?_, ?_, ?_, ?_, ?_⟩
  · unfold fig; rw [ap1, ap2, ap3]
  · unfold fig; rw [b11, b12, b13]
  · unfold fig; rw [b21, b22, b23]
  · unfold cnt fig; exact hid
  · unfold cnt fig at *; omega

/-- **The three balance equations admit exactly one relation** (rank 2): given the `α`-balance, the
`β`-balance and `γ`-balance together are equivalent to the single identity `v₁ = 1 + n₂ + v₃ + 2v₄`. -/
theorem census_equations_equiv {N n1 n2 v1 v2 v3 v4 : ℕ} :
    (3 + n1 + 3 * n2 + 2 * v2 + 4 * v3 + 6 * v4 = N ∧
      2 + n1 + 2 * n2 + v1 + 2 * v2 + 3 * v3 + 4 * v4 = N ∧ n1 + 3 * v1 + 2 * v2 + v3 = N)
    ↔ (3 + n1 + 3 * n2 + 2 * v2 + 4 * v3 + 6 * v4 = N ∧ v1 = 1 + n2 + v3 + 2 * v4) := by
  omega

end Erdos634.Draft.LemCensusFormal

#print axioms Erdos634.Draft.LemCensusFormal.lem_census_exact
#print axioms Erdos634.Draft.LemCensusFormal.census_equations_equiv
