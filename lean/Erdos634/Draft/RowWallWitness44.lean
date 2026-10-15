-- Non-vacuity witnesses, on the kernel-checked N = 44 tiling
-- (`ApexWitness44.D44`, m = 2), for the frame-free generic helpers of the row-wall development
-- (Draft/RowWallLocal.lean, Draft/RowWallReal.lean): `edge_idx`, `flank_of_range`, `pair_cases`,
-- `ident`, `side_of_across` have all hypotheses discharged on the first tile of `D44`.
-- Frame-bound statements (`LFrame`, `CH`, the local lemmas `slot_int`, `junc_kill`, `row_all_a`,
-- `matched_word`, `ad_all`, `r8_corner`, ...) take an `HFrame`, i.e. an `m = 1` member with
-- `2 ≤ e ≤ f − 2`; `D44` is `e = 1, f = 2, m = 2`, so no `HFrame` exists on it.
import Erdos634.Draft.LemmaGCornerReal
import Erdos634.Draft.ApexWitness44

namespace Erdos634.Draft.RowWallWitness44

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.Draft.CornerAdjacency
open Erdos634.Draft.RowWallReal Erdos634.Draft.ApexWitness44

/-- The first tile of the real 44-tiling. -/
noncomputable def T0 : Tri := D44.tile ⟨0, by decide⟩

/-- `edge_idx`: two distinct vertices of a real tile are the ends of an edge. -/
theorem w_edge_idx : ∃ m : Fin 3, (T0.pts m = T0.pts 0 ∧ T0.pts (m + 1) = T0.pts 1) ∨
    (T0.pts m = T0.pts 1 ∧ T0.pts (m + 1) = T0.pts 0) :=
  edge_idx ⟨0, rfl⟩ ⟨1, rfl⟩ (pts_ne T0 (by decide))

/-- `flank_of_range` and `ident` on the real tile: its corner `0` with flank pair
`(pts 1 − pts 0, pts 2 − pts 0)` is identified from the flanks. -/
theorem w_flank_ident : ∃ m, (D44.tile ⟨0, by decide⟩).pts m = T0.pts 0 ∧
    IsFlankPair (D44.tile ⟨0, by decide⟩) m (T0.pts 0) (T0.pts 1 - T0.pts 0) (T0.pts 2 - T0.pts 0) ∧
    Set.range (D44.tile ⟨0, by decide⟩).pts =
      {T0.pts 0, T0.pts 0 + (T0.pts 1 - T0.pts 0), T0.pts 0 + (T0.pts 2 - T0.pts 0)} := by
  have hr : Set.range (D44.tile ⟨0, by decide⟩).pts = {T0.pts 0, T0.pts 1, T0.pts 2} := by
    exact MarchInduction.range_pts_eq _
  obtain ⟨m, hm, hfl⟩ := flank_of_range hr
  have hc := ApexPlacement.flank_cross_ne hm hfl
  refine ⟨m, hm, hfl, ident hm hfl rfl ?_ (mul_self_pos.mpr hc) rfl rfl⟩
  intro h; apply hc; rw [h, NearBaseVertex.cross_apply]; simp

/-- `pair_cases` on the real tile's edge `(0,1)`. -/
theorem w_pair_cases : (T0.pts 0 = T0.pts 0 ∧ T0.pts 1 = T0.pts 1) ∨
    (T0.pts 0 = T0.pts 1 ∧ T0.pts 1 = T0.pts 0) :=
  pair_cases rfl (pts_ne T0 (by decide))

/-- `side_of_across`: a flank `W'` across `ℝU₀` from `W₀`, and a candidate `W₁` across as well,
are on the same side (instance: the real tile's own flanks, `W' = W₁ = −W₀`). -/
theorem w_side_of_across : 0 < cross (T0.pts 1 - T0.pts 0) (-(T0.pts 2 - T0.pts 0)) *
    cross (T0.pts 1 - T0.pts 0) (-(T0.pts 2 - T0.pts 0)) := by
  have hr : Set.range (D44.tile ⟨0, by decide⟩).pts = {T0.pts 0, T0.pts 1, T0.pts 2} := by
    exact MarchInduction.range_pts_eq _
  obtain ⟨m, hm, hfl⟩ := flank_of_range hr
  have hc := ApexPlacement.flank_cross_ne hm hfl
  have hneg : cross (T0.pts 1 - T0.pts 0) (T0.pts 2 - T0.pts 0) *
      cross (T0.pts 1 - T0.pts 0) (T0.pts 2 - T0.pts 0) > 0 := mul_self_pos.mpr hc
  have h1 : cross (T0.pts 1 - T0.pts 0) (-(T0.pts 2 - T0.pts 0)) *
      cross (T0.pts 1 - T0.pts 0) (T0.pts 2 - T0.pts 0) < 0 := by
    rw [show -(T0.pts 2 - T0.pts 0) = (-1 : ℝ) • (T0.pts 2 - T0.pts 0) by simp, cross_smul_right]
    nlinarith
  exact side_of_across one_pos (one_smul ℝ _).symm h1 h1

end Erdos634.Draft.RowWallWitness44

#print axioms Erdos634.Draft.RowWallWitness44.w_edge_idx
#print axioms Erdos634.Draft.RowWallWitness44.w_flank_ident
#print axioms Erdos634.Draft.RowWallWitness44.w_pair_cases
#print axioms Erdos634.Draft.RowWallWitness44.w_side_of_across
