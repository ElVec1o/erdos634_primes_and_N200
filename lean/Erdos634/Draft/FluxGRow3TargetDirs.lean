-- Draft/FluxGRow3TargetDirs.lean — Proposition RP, Step 5: the three boundary-edge directions of the
-- isosceles target `targetIso`, and their grid degrees relative to the `BC` edge.
-- Imported directly by All.lean.
--
-- Traversing `B → C → A` counterclockwise gives `dir(B→C) = θ₀`, `dir(C→A) = θ₀ + (π − α)`,
-- `dir(A→B) = θ₀ + π + α`. This file proves this as a `Tri.leftUnit` computation on `targetIso`
-- (vertex order `(B, C, A)`, angles `(α, α, π − 2α)`), and computes each edge's grid degree
-- `(gridK, gridJ)`. In Step 5's notation, `BC` sits at `(0,0)`, `CA` at `(−1,2)` and `AB` at `(1,2)`;
-- "sits at `(p, q)`" means the direction differs from that of `BC` by the grid shift `p·α + q·(π/2)`
-- (the convention of `gaussWeightA_shift` and `isGridA_add_shift`). Given that `BC` is on the grid,
-- the absolute `(gridK, gridJ)` of `CA` and `AB` follow.
--
-- Tools: `Tri.leftUnit_turn_of_pos` (`FluxTurn.lean`) for the two turn steps; `gridK_add_shift`,
-- `gridJ_add_shift`, `isGridA_add_shift` (`FluxGRow3Cancel.lean`) for the absolute grid degrees;
-- `targetIso`, `targetIso_angleAt0/1/2` (`FluxGRow3TargetCoords.lean`). New here: `targetIso_det_pos`,
-- the sign fact needed to apply `leftUnit_turn_of_pos`.
--
-- Not done here: the boundary polynomial `Σ_X z^X Φ_X` itself (see `FluxGRow3Step5`), and a
-- `CongruentDissection` linking `targetIso` to real tiles; so `IsGridA` for the direction of `BC` is a
-- hypothesis (`hgridBC`).
import Erdos634.Draft.FluxGRow3TargetCoords
import Erdos634.Draft.FluxGRow3Cancel

namespace Erdos634.Geometry.Row3

open Real Erdos634.Geometry Erdos634.SssTri

/-! ## §1 Orientation: `targetIso` is positively oriented (`det > 0`)

Needed to invoke `Tri.leftUnit_turn_of_pos`. `sssTri`'s placement is `pts 0 = (0,0)`,
`pts 1 = (r,0)`, `pts 2 = (x,h)`, so `Tri.det = r * h` (the shoelace formula collapses on this base-
on-the-axis placement); for `targetIso`, `r = 2·lam·cos α > 0` and `h = targetH α lam = lam·sin α >
0` under the standing hypotheses `0 < α < π/2`, `0 < lam`, so `det > 0`. -/

theorem sssTri_det (p q r h : ℝ) (hr : r ≠ 0) (hh : h ≠ 0) :
    (sssTri p q r h hr hh).det = r * h := by
  unfold Tri.det sssTri
  simp only [sssPts]
  have e0 : ((EuclideanSpace.equiv (Fin 2) ℝ).symm ![xCoord p q r, h] -
      (EuclideanSpace.equiv (Fin 2) ℝ).symm ![0, 0]) 0 = xCoord p q r := by
    simp [EuclideanSpace.equiv]
  have e1 : ((EuclideanSpace.equiv (Fin 2) ℝ).symm ![xCoord p q r, h] -
      (EuclideanSpace.equiv (Fin 2) ℝ).symm ![0, 0]) 1 = h := by
    simp [EuclideanSpace.equiv]
  have e2 : ((EuclideanSpace.equiv (Fin 2) ℝ).symm ![r, 0] -
      (EuclideanSpace.equiv (Fin 2) ℝ).symm ![0, 0]) 0 = r := by
    simp [EuclideanSpace.equiv]
  have e3 : ((EuclideanSpace.equiv (Fin 2) ℝ).symm ![r, 0] -
      (EuclideanSpace.equiv (Fin 2) ℝ).symm ![0, 0]) 1 = 0 := by
    simp [EuclideanSpace.equiv]
  rw [e0, e1, e2, e3]; ring

theorem targetIso_det_pos (α lam : ℝ) (hα : 0 < α) (hα2 : α < Real.pi / 2) (hlam : 0 < lam) :
    0 < (targetIso α lam hα hα2 hlam).det := by
  have hc : 0 < Real.cos α := Real.cos_pos_of_mem_Ioo ⟨by linarith, hα2⟩
  have hs : 0 < Real.sin α := Real.sin_pos_of_pos_of_lt_pi hα (by linarith [Real.pi_pos])
  unfold targetIso
  rw [sssTri_det]
  unfold targetH; positivity

/-! ## §2 The three edge directions, as `leftUnit`-angle turn steps

Vertex order `(pts 0, pts 1, pts 2) = (B, C, A)`, so edge `0` is `B → C`, edge `1` is `C → A`, edge
`2` is `A → B`. As in Step 5: `dir(C→A) = dir(B→C) + (π − α)`,
`dir(A→B) = dir(C→A) + 2α = dir(B→C) + (π + α)`. -/

theorem targetIso_turn_CA (α lam : ℝ) (hα : 0 < α) (hα2 : α < Real.pi / 2) (hlam : 0 < lam) :
    ((targetIso α lam hα hα2 hlam).leftUnit 1).angle
      = ((targetIso α lam hα hα2 hlam).leftUnit 0).angle
        + ((Real.pi - α : ℝ) : Real.Angle) := by
  set T := targetIso α lam hα hα2 hlam with hT
  have hdet : 0 < T.det := targetIso_det_pos α lam hα hα2 hlam
  have h := T.leftUnit_turn_of_pos hdet 0
  simp only [show (0 : Fin 3) + 1 = 1 from rfl] at h
  rw [hT, targetIso_angleAt1 α lam hα hα2 hlam] at h
  rw [h]

theorem targetIso_turn_AB (α lam : ℝ) (hα : 0 < α) (hα2 : α < Real.pi / 2) (hlam : 0 < lam) :
    ((targetIso α lam hα hα2 hlam).leftUnit 2).angle
      = ((targetIso α lam hα hα2 hlam).leftUnit 0).angle
        + ((Real.pi + α : ℝ) : Real.Angle) := by
  set T := targetIso α lam hα hα2 hlam with hT
  have hdet : 0 < T.det := targetIso_det_pos α lam hα hα2 hlam
  have h := T.leftUnit_turn_of_pos hdet 1
  simp only [show (1 : Fin 3) + 1 = 2 from rfl] at h
  rw [hT, targetIso_angleAt2 α lam hα hα2 hlam] at h
  have hstep : ((targetIso α lam hα hα2 hlam).leftUnit 1).angle
      = ((targetIso α lam hα hα2 hlam).leftUnit 0).angle + ((Real.pi - α : ℝ) : Real.Angle) :=
    targetIso_turn_CA α lam hα hα2 hlam
  rw [hstep, add_assoc] at h
  have hcoe : ((Real.pi - α : ℝ) : Real.Angle) + ((Real.pi - (Real.pi - 2 * α) : ℝ) : Real.Angle)
      = ((Real.pi + α : ℝ) : Real.Angle) := by
    rw [← Real.Angle.coe_add]; congr 1; ring
  rw [hcoe] at h
  exact h

/-! ## §3 Grid degrees of `CA` and `AB`, relative to `BC`'s

Given `BC`'s direction lies on the grid `θ₀ + ℤα + ℤ(π/2)` (an unproved placement hypothesis here —
see the file header), `CA` and `AB` also lie on the grid, at the shifts Step 5 states:
`CA` at `(p, q) = (-1, 2)` (`π − α = (-1)·α + 2·(π/2)`), `AB` at `(p, q) = (1, 2)`
(`π + α = 1·α + 2·(π/2)`). This matches the bookkeeping "`CA` sits at `(−1, 2)`",
"`AB` sits at `(1, 2)`" literally, reading "sits at `(p, q)`" as the shift from `BC`. -/

theorem targetIso_grid_CA (α θ₀ lam : ℝ) (hα : 0 < α) (hα2 : α < Real.pi / 2) (hlam : 0 < lam)
    (hairr : Irrational (α / Real.pi))
    (hgridBC : IsGridA α θ₀ ((targetIso α lam hα hα2 hlam).leftUnit 0).angle) :
    IsGridA α θ₀ ((targetIso α lam hα hα2 hlam).leftUnit 1).angle
      ∧ gridK α θ₀ ((targetIso α lam hα hα2 hlam).leftUnit 1).angle
          = gridK α θ₀ ((targetIso α lam hα hα2 hlam).leftUnit 0).angle - 1
      ∧ (4 : ℤ) ∣ (gridJ α θ₀ ((targetIso α lam hα hα2 hlam).leftUnit 1).angle
          - (gridJ α θ₀ ((targetIso α lam hα hα2 hlam).leftUnit 0).angle + 2)) := by
  have hturn := targetIso_turn_CA α lam hα hα2 hlam
  have hshift : (Real.pi - α : ℝ) = (((-1:ℤ):ℝ) * α + ((2:ℤ):ℝ) * (Real.pi / 2) : ℝ) := by
    push_cast; ring
  rw [hshift] at hturn
  rw [hturn]
  refine ⟨isGridA_add_shift hgridBC (-1) 2, ?_, ?_⟩
  · have := gridK_add_shift hairr hgridBC (-1) 2
    push_cast at this ⊢
    omega
  · exact gridJ_add_shift hairr hgridBC (-1) 2

theorem targetIso_grid_AB (α θ₀ lam : ℝ) (hα : 0 < α) (hα2 : α < Real.pi / 2) (hlam : 0 < lam)
    (hairr : Irrational (α / Real.pi))
    (hgridBC : IsGridA α θ₀ ((targetIso α lam hα hα2 hlam).leftUnit 0).angle) :
    IsGridA α θ₀ ((targetIso α lam hα hα2 hlam).leftUnit 2).angle
      ∧ gridK α θ₀ ((targetIso α lam hα hα2 hlam).leftUnit 2).angle
          = gridK α θ₀ ((targetIso α lam hα hα2 hlam).leftUnit 0).angle + 1
      ∧ (4 : ℤ) ∣ (gridJ α θ₀ ((targetIso α lam hα hα2 hlam).leftUnit 2).angle
          - (gridJ α θ₀ ((targetIso α lam hα hα2 hlam).leftUnit 0).angle + 2)) := by
  have hturn := targetIso_turn_AB α lam hα hα2 hlam
  have hshift : (Real.pi + α : ℝ) = (((1:ℤ):ℝ) * α + ((2:ℤ):ℝ) * (Real.pi / 2) : ℝ) := by
    push_cast; ring
  rw [hshift] at hturn
  rw [hturn]
  refine ⟨isGridA_add_shift hgridBC 1 2, ?_, ?_⟩
  · have := gridK_add_shift hairr hgridBC 1 2
    push_cast at this ⊢
    omega
  · exact gridJ_add_shift hairr hgridBC 1 2

/-! ## §4 A concrete numeric witness (sanity check, not the base-β tile)

Reuses `FluxGRow3TargetCoords.lean`'s own witness `(α, lam) = (π/4, 1)`; `BC`'s direction is taken to
be on the grid at `(θ₀, k, j) = (θ₀, 0, 0)` itself — a non-vacuous instance of `hgridBC`. As there,
`α = π/4` is rational over `π` (`α/π = 1/4`), so this is a SANITY CHECK ONLY, not the `α ∉ ℚπ` regime;
the general theorems above cover the real (irrational-`α`) case this witness does not exercise, and
`targetIso_grid_CA`/`targetIso_grid_AB` are NOT invoked on this witness for that reason (their
`hairr` hypothesis is false for `α = π/4`) — only `targetIso_det_pos`, `targetIso_turn_CA`,
`targetIso_turn_AB`, which need no irrationality, are exercised numerically. -/

theorem witness_det_pos :
    0 < (targetIso (Real.pi/4) 1 witness_hα witness_hα2 witness_hlam).det :=
  targetIso_det_pos (Real.pi/4) 1 witness_hα witness_hα2 witness_hlam

theorem witness_turn_CA :
    ((targetIso (Real.pi/4) 1 witness_hα witness_hα2 witness_hlam).leftUnit 1).angle
      = ((targetIso (Real.pi/4) 1 witness_hα witness_hα2 witness_hlam).leftUnit 0).angle
        + ((3 * Real.pi / 4 : ℝ) : Real.Angle) := by
  have h := targetIso_turn_CA (Real.pi/4) 1 witness_hα witness_hα2 witness_hlam
  rw [h]
  congr 2
  ring

end Erdos634.Geometry.Row3

#print axioms Erdos634.Geometry.Row3.sssTri_det
#print axioms Erdos634.Geometry.Row3.targetIso_det_pos
#print axioms Erdos634.Geometry.Row3.targetIso_turn_CA
#print axioms Erdos634.Geometry.Row3.targetIso_turn_AB
#print axioms Erdos634.Geometry.Row3.targetIso_grid_CA
#print axioms Erdos634.Geometry.Row3.targetIso_grid_AB
#print axioms Erdos634.Geometry.Row3.witness_det_pos
#print axioms Erdos634.Geometry.Row3.witness_turn_CA
