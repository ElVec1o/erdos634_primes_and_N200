/-
Draft/WGapRay.lean -- written 15 November 2026.  UNAUDITED beyond internal checks; hand proof WGAP_PROOF_2026-11-15.
Not imported by any aggregate.  Module W3c: the wedge API, part B (GEOMETRY: the filler adjacent to a bounding ray).

`ray_filler`: let `t₀` be a tile with an edge `[X, Y]` (third vertex `Z` strictly on the left of the directed line `X → Y`), `P'` a point of the line
beyond `X` (so `X ∈ (P', Y)`), the open segment `(X, Y)` interior to the target, and the clamp "no chain edge of the line `F = c` straddles `X`" (the
hand proof's "the direction beyond `X` is interior to a tile or outside Δ").  Then a tile `τ ≠ t₀` on the RIGHT of the line has vertices `X` and
`X + t (Y - X)`, `t > 0`: the tile adjacent to the ray `X → Y` on the wedge side, with an edge on the ray starting at `X`.  This is `SideRunTools.next_tile`
for the functional `crossL (Y - X)`, with the wall hypothesis discharged by `seg_wall` and the distinctness `τ ≠ t₀` from `Z`.
Also `edge_len_on_ray`: the length of that edge is `a`, `b` or `c`.
No sorry, no native_decide.
-/
import Erdos634.Draft.WGapWedge2

open scoped Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Erdos634.Draft.WGapStmt

open Erdos634.Geometry Erdos634.CertCoord Erdos634.MarchKillsFan Erdos634.MarchSlots
  Erdos634.MarchInduction Erdos634.MarchKills Erdos634.BaseBetaTargetCoord Erdos634.MarchCompose
  Erdos634.RunPartition Erdos634.E1BaseWord Erdos634.WallEndpoints Erdos634.BaseChain
  Erdos634.Placement Erdos634.OrientBridge Erdos634.ChainInstance Erdos634.TilePlacement
  Erdos634.Geometry.Dissection Erdos634.Draft.W2E1 Erdos634.Draft.SideRun Erdos634.Draft.SideRunG
  Erdos634.Draft.SideRunGJ Erdos634.Draft.SideRunGA Set

variable {N : ℕ} {D : CongruentDissection N}

theorem crossL_ne_zero {u : Plane} (hu : u ≠ 0) : crossL u ≠ 0 := by
  intro h
  have h1 := congrArg (fun F : Plane →ₗ[ℝ] ℝ => F (mkPt (-(u 1)) (u 0))) h
  simp only [crossL_apply, LinearMap.zero_apply, cross, mkPt_zero, mkPt_one] at h1
  apply hu
  ext i
  fin_cases i
  · simp; nlinarith [sq_nonneg (u 0), sq_nonneg (u 1)]
  · simp; nlinarith [sq_nonneg (u 0), sq_nonneg (u 1)]

/-- **API part B: the filler adjacent to a bounding ray** -/
theorem ray_filler (D : CongruentDissection N) {X Y P' Z : Plane} {t₀ : Fin N} (hXY : X ≠ Y)
    (hV : HasV D t₀ X Y Z) (hZ : 0 < cross (Y - X) (Z - X))
    (hP' : cross (Y - X) (P' - X) = 0) (hXP : X ∈ openSegment ℝ P' Y)
    (hint : openSegment ℝ X Y ⊆ interior D.target.carrier)
    (hclamp : ∀ ed ∈ D.lineChain (crossL (Y - X)) (cross (Y - X) X),
      ¬ Straddles ((D.tile ed.1).edge ed.2) P' X Y) :
    ∃ (τ : Fin N) (k m : Fin 3) (t : ℝ), τ ≠ t₀ ∧ k ≠ m ∧ (D.tile τ).pts k = X ∧ 0 < t ∧
      (D.tile τ).pts m = AffineMap.lineMap X Y t ∧
      ∀ j, cross (Y - X) ((D.tile τ).pts j - X) ≤ 0 := by
  have hu : Y - X ≠ 0 := sub_ne_zero.mpr (Ne.symm hXY)
  have hF := crossL_ne_zero hu
  have hfX : crossL (Y - X) X = cross (Y - X) X := crossL_apply _ _
  have hfY : crossL (Y - X) Y = cross (Y - X) X := by
    rw [crossL_apply]
    have : cross (Y - X) Y = cross (Y - X) (Y - X) + cross (Y - X) X := by
      rw [← cross_add_right]; congr 1; abel
    rw [this]
    simp [cross]
    ring
  have hfP' : crossL (Y - X) P' = cross (Y - X) X := by
    rw [crossL_apply]
    have : cross (Y - X) P' = cross (Y - X) (P' - X) + cross (Y - X) X := by
      rw [← cross_add_right]; congr 1; abel
    rw [this, hP']; ring
  have hwall : ∀ y ∈ openSegment ℝ X Y, ∀ i, y ∉ interior (D.tile i).carrier := by
    intro y hy
    obtain ⟨k, m, j, hkm, hkj, hmj, hk, hm, hj⟩ := hV
    refine seg_wall D.toDissection (t := t₀) hkm ?_
    rw [hk, hm]; exact openSegment_subset_segment ℝ _ _ hy
  obtain ⟨ed, hed, k, m, t, hkm, hk, ht, hm, hle, -, -⟩ :=
    next_tile D.toDissection (crossL (Y - X)) hF (cross (Y - X) X) hXY.symm.symm hfX hfY hfP' hXP hint hwall hclamp
  refine ⟨ed.1, k, m, t, ?_, hkm, hk, ht, hm, fun j => ?_⟩
  · rintro rfl
    obtain ⟨kk, mm, jj, hkm', hkj', hmj', hk', hm', hj'⟩ := hV
    have := hle jj
    rw [hj', crossL_apply] at this
    have h2 : cross (Y - X) Z = cross (Y - X) (Z - X) + cross (Y - X) X := by
      rw [← cross_add_right]; congr 1; abel
    linarith
  · have := hle j
    rw [crossL_apply] at this
    have h2 : cross (Y - X) ((D.tile ed.1).pts j) = cross (Y - X) ((D.tile ed.1).pts j - X) + cross (Y - X) X := by
      rw [← cross_add_right]; congr 1; abel
    linarith

end Erdos634.Draft.WGapStmt
