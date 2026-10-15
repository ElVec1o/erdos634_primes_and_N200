import Erdos634.CornerAnglePermCensus

/-!
# CornerAnglePermCensus: vertex-figure census for congruent dissections
Key results:
- `congruentDissection_vertex_census`: under the base-β angle relations, the count of
  `(0,1,3)`-figure vertices equals 1 + (3,2,0)-count + (4,3,1)-count + 2×(6,4,0)-count.
- `congruentDissection_climber_mandatory`: at least one `(0,1,3)`-figure vertex exists,
  i.e. the climber figure is mandatory.
No sorry.
-/

namespace Erdos634.Draft.CornerAnglePermCensusWrap

open Erdos634.Geometry

/-- Wrap: vertex census identity for a congruent dissection satisfying the base-β angle
    relations `γ = 2α + β`, `3α + 2β = π`, with `α` irrational over `π`. -/
theorem congruentDissection_vertex_census_wrap {N : ℕ} (D : CongruentDissection N) (α β γ : ℝ)
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hαπ : α ≠ Real.pi) (hα2π : α ≠ 2 * Real.pi) (hα0 : α ≠ 0)
    (hβγ : β ≠ γ) (hβπ : β ≠ Real.pi) (hβ2π : β ≠ 2 * Real.pi) (hβ0 : β ≠ 0)
    (hγπ : γ ≠ Real.pi) (hγ2π : γ ≠ 2 * Real.pi) (hγ0 : γ ≠ 0)
    (hπ2π : Real.pi ≠ 2 * Real.pi) (hπ0 : Real.pi ≠ 0) (h2π0 : 2 * Real.pi ≠ 0)
    (hmα : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hmβ : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hmγ : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    (hγdef : γ = 2 * α + β) (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (htarget : ∀ k : Fin 3,
      cornerAngle (D.target.pts (k + 1)) (D.target.pts k) (D.target.pts (k + 2)) = 3 * α ∨
      cornerAngle (D.target.pts (k + 1)) (D.target.pts k) (D.target.pts (k + 2)) = β) :
    ((cornerPts D.toDissection).filter (fun v =>
      ((({i | (D.tile i).localAngle v = α} : Finset (Fin N)).card,
        ({i | (D.tile i).localAngle v = β} : Finset (Fin N)).card,
        ({i | (D.tile i).localAngle v = γ} : Finset (Fin N)).card) : ℕ × ℕ × ℕ)
        = (0, 1, 3))).card
      = 1 + ((cornerPts D.toDissection).filter (fun v =>
      ((({i | (D.tile i).localAngle v = α} : Finset (Fin N)).card,
        ({i | (D.tile i).localAngle v = β} : Finset (Fin N)).card,
        ({i | (D.tile i).localAngle v = γ} : Finset (Fin N)).card) : ℕ × ℕ × ℕ)
        = (3, 2, 0))).card
        + ((cornerPts D.toDissection).filter (fun v =>
      ((({i | (D.tile i).localAngle v = α} : Finset (Fin N)).card,
        ({i | (D.tile i).localAngle v = β} : Finset (Fin N)).card,
        ({i | (D.tile i).localAngle v = γ} : Finset (Fin N)).card) : ℕ × ℕ × ℕ)
        = (4, 3, 1))).card
        + 2 * ((cornerPts D.toDissection).filter (fun v =>
      ((({i | (D.tile i).localAngle v = α} : Finset (Fin N)).card,
        ({i | (D.tile i).localAngle v = β} : Finset (Fin N)).card,
        ({i | (D.tile i).localAngle v = γ} : Finset (Fin N)).card) : ℕ × ℕ × ℕ)
        = (6, 4, 0))).card :=
  congruentDissection_vertex_census D α β γ hαβ hαγ hαπ hα2π hα0 hβγ hβπ hβ2π hβ0
    hγπ hγ2π hγ0 hπ2π hπ0 h2π0 hmα hmβ hmγ hγdef hrel hirr htarget

/-- Wrap: under the same hypotheses, the climber vertex figure `(0,1,3)` occurs at least once. -/
theorem congruentDissection_climber_mandatory_wrap {N : ℕ} (D : CongruentDissection N) (α β γ : ℝ)
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hαπ : α ≠ Real.pi) (hα2π : α ≠ 2 * Real.pi) (hα0 : α ≠ 0)
    (hβγ : β ≠ γ) (hβπ : β ≠ Real.pi) (hβ2π : β ≠ 2 * Real.pi) (hβ0 : β ≠ 0)
    (hγπ : γ ≠ Real.pi) (hγ2π : γ ≠ 2 * Real.pi) (hγ0 : γ ≠ 0)
    (hπ2π : Real.pi ≠ 2 * Real.pi) (hπ0 : Real.pi ≠ 0) (h2π0 : 2 * Real.pi ≠ 0)
    (hmα : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hmβ : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hmγ : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    (hγdef : γ = 2 * α + β) (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (htarget : ∀ k : Fin 3,
      cornerAngle (D.target.pts (k + 1)) (D.target.pts k) (D.target.pts (k + 2)) = 3 * α ∨
      cornerAngle (D.target.pts (k + 1)) (D.target.pts k) (D.target.pts (k + 2)) = β) :
    1 ≤ ((cornerPts D.toDissection).filter (fun v =>
      ((({i | (D.tile i).localAngle v = α} : Finset (Fin N)).card,
        ({i | (D.tile i).localAngle v = β} : Finset (Fin N)).card,
        ({i | (D.tile i).localAngle v = γ} : Finset (Fin N)).card) : ℕ × ℕ × ℕ)
        = (0, 1, 3))).card :=
  congruentDissection_climber_mandatory D α β γ hαβ hαγ hαπ hα2π hα0 hβγ hβπ hβ2π hβ0
    hγπ hγ2π hγ0 hπ2π hπ0 h2π0 hmα hmβ hmγ hγdef hrel hirr htarget

example : True := trivial

#print axioms congruentDissection_vertex_census_wrap
#print axioms congruentDissection_climber_mandatory_wrap

end Erdos634.Draft.CornerAnglePermCensusWrap
