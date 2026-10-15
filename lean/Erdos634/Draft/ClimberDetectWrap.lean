import Erdos634.OrderForcing
import Erdos634.CornerAnglePermCensus

/-!
# Climbers detect deviation: wrapper

At an interior lattice point of the brick/mate structure
exactly six tiles meet; counts are (2,2,2) so the figure is {2α,2β,2γ}. Hence {β,3γ} never
occurs at a brick/mate point. By the vertex census identity and the charge count, each escape
requires two deviation points.

Lean content:
1. **`climberdetect_brickmate_figure`**: brick/mate vertex arithmetic (2+2*2=6 ∧ 2+2=4).
2. **`climberdetect_mandatory`**: every real CongruentDissection has ≥1 climber vertex.
3. **`climberdetect_escape_charge`**: if n₂≥1 then v₁≥2 (two climbers forced by escape).

Only the arithmetic and the mandatory climber are formalized.  'Brick/mate structure' and
'interior lattice point' are not defined in Lean; the "detector, not exclusion" interpretation is
a placement statement.
-/

namespace Erdos634.Draft.ClimberDetectWrap

open Erdos634.OrderForcing Erdos634.Geometry

/-- lem:climberdetect (i): brick/mate vertex figure arithmetic: six tiles, counts (2,2,2). -/
theorem climberdetect_brickmate_figure : 2 + 2 * 2 = 6 ∧ 2 + 2 = 4 :=
  brick_mate_vertex

/-- lem:climberdetect (ii): every real CongruentDissection has ≥1 {β,3γ} climber vertex. -/
theorem climberdetect_mandatory {N : ℕ} (D : CongruentDissection N) (α β γ : ℝ)
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

/-- lem:climberdetect (iii): if n₂≥1 (mirrored cover piece forced), then v₁≥2 (two climbers). -/
theorem climberdetect_escape_charge {N n1 n2 v1 v2 v3 v4 : ℕ} (hn2 : 1 ≤ n2)
    (ha : 3 + n1 + 3 * n2 + 2 * v2 + 4 * v3 + 6 * v4 = N)
    (hb : 2 + n1 + 2 * n2 + v1 + 2 * v2 + 3 * v3 + 4 * v4 = N)
    (hg : n1 + 3 * v1 + 2 * v2 + v3 = N) : 2 ≤ v1 :=
  escape_charge hn2 ha hb hg

#print axioms climberdetect_brickmate_figure
#print axioms climberdetect_mandatory
#print axioms climberdetect_escape_charge

end Erdos634.Draft.ClimberDetectWrap
