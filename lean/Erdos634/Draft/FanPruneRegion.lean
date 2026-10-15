import Erdos634.Draft.RegionTiling
import Erdos634.AngleSumDissection
import Erdos634.PinPlumbing
import Erdos634.CongruentAngles

/-!
# Soundness of the fan-collapse prune, for a region

Let a convex corner of the uncovered region have angle `W`, and let the tile's angles be
`α < β ≤ γ`.  If `W < β` then every tile angle at the corner equals `α`, so `W = kα` for `k` the number
of tiles there; consequently a corner with `W < β` that is not an integer multiple of `α` admits no
completion.

`FanPruneSound` holds the multiset arithmetic.  What is needed here is the bridge from a region to the
multiset: that the tiles of a completion have vertices at the corner and that their angles there
sum to `W`.  It is proved by the measure route of `AngleSumDissection`, which never used that
the tiled set is a triangle.

* `ConvexCornerAt S p W` : near `p` the set `S` coincides with a triangle that has a vertex at `p`
  with angle `W` (so `S` is locally a wedge of angle `W`).
* `sum_localAngle_corner` : for a tiling of `S` (`RegionTiling.RTiling`), the local angles of the
  tiles at `p` sum to `W`.
* `fan_prune_region` : if `W < β ≤ γ`, every tile's local angle at `p` is `α` or `0`, and
  `W = k·α` with `k` the number of tiles with local angle `α` there.  (No tile has `p` inside an
  edge or in its interior, and no tile presents `β` or `γ`.)
* `fan_prune_no_completion` : if moreover `W` is not a natural multiple of `α`, the region has no
  tiling by copies of the tile, with any number of tiles.
* `convexCornerAt_tri` : a triangle has a convex corner at each of its vertices (the hypothesis is
  satisfiable).

Standard axioms, no `sorry`.
-/

open MeasureTheory Set Metric
open scoped ENNReal Classical
open Erdos634 Erdos634.Geometry Erdos634.Draft.RegionTiling

namespace Erdos634.Draft.FanPruneRegion

/-- `S` has a convex corner of angle `W` at `p`: near `p` it coincides with a triangle having a
vertex at `p` whose angle is `W`. -/
def ConvexCornerAt (S : Set Plane) (p : Plane) (W : ℝ) : Prop :=
  ∃ T : Tri, ∃ k : Fin 3, T.pts k = p ∧
    cornerAngle (T.pts (k + 1)) (T.pts k) (T.pts (k + 2)) = W ∧
    ∃ r0 > 0, S ∩ Metric.ball p r0 = T.carrier ∩ Metric.ball p r0

/-- A triangle has a convex corner at each vertex. -/
theorem convexCornerAt_tri (T : Tri) (k : Fin 3) :
    ConvexCornerAt T.carrier (T.pts k)
      (cornerAngle (T.pts (k + 1)) (T.pts k) (T.pts (k + 2))) :=
  ⟨T, k, rfl, rfl, 1, one_pos, rfl⟩

variable {S : Set Plane} {M : Tri} {n : ℕ}

theorem aedisjoint_tiles (R : RTiling S M n) {i j : Fin n} (hij : i ≠ j) :
    AEDisjoint volume (R.tile i).carrier (R.tile j).carrier := by
  have hsub : (R.tile i).carrier ∩ (R.tile j).carrier ⊆
      frontier (R.tile i).carrier ∪ frontier (R.tile j).carrier := by
    rintro x ⟨hxi, hxj⟩
    by_cases h1 : x ∈ interior (R.tile i).carrier
    · by_cases h2 : x ∈ interior (R.tile j).carrier
      · exfalso
        exact Set.disjoint_left.mp (R.disj hij) h1 h2
      · exact Or.inr ⟨subset_closure hxj, h2⟩
    · exact Or.inl ⟨subset_closure hxi, h1⟩
  refine measure_mono_null hsub ?_
  exact measure_union_null (R.tile i).volume_frontier (R.tile j).volume_frontier

theorem volume_inter_ball_eq_sum (R : RTiling S M n) (x : Plane) (r : ℝ) :
    volume (S ∩ Metric.ball x r) = ∑ i, volume ((R.tile i).carrier ∩ Metric.ball x r) := by
  have h := measure_biUnion_finset₀ (μ := volume)
    (s := (Finset.univ : Finset (Fin n)))
    (f := fun i => (R.tile i).carrier ∩ Metric.ball x r)
    (fun i _ j _ hij => measure_mono_null
      (Set.inter_subset_inter Set.inter_subset_left Set.inter_subset_left)
      (aedisjoint_tiles R hij))
    (fun i _ => ((R.tile i).nullMeasurableSet).inter
      Metric.isOpen_ball.measurableSet.nullMeasurableSet)
  have hU : (⋃ i ∈ (Finset.univ : Finset (Fin n)), ((R.tile i).carrier ∩ Metric.ball x r))
          = S ∩ Metric.ball x r := by
    simp only [Finset.mem_univ, Set.iUnion_true]
    rw [← Set.iUnion_inter, R.covers]
  rw [hU] at h
  exact h

/-- A tiled region with a point has at least one tile. -/
theorem pos_of_mem (R : RTiling S M n) {p : Plane} (hp : p ∈ S) : 0 < n := by
  rw [← R.covers] at hp
  obtain ⟨i, _⟩ := Set.mem_iUnion.mp hp
  exact Nat.pos_of_ne_zero (fun h => by subst h; exact i.elim0)

/-- **The angle sum at a convex corner of a tiled region.** -/
theorem sum_localAngle_corner (R : RTiling S M n) {p : Plane} {W : ℝ}
    (hc : ConvexCornerAt S p W) : ∑ i, (R.tile i).localAngle p = W := by
  obtain ⟨T, k, hk, hW, r0, hr0, hS⟩ := hc
  have hTp : T.localAngle p = W := by rw [← hk, T.localAngle_vertex k, hW]
  have hpS : p ∈ S := by
    have hpT : p ∈ T.carrier ∩ Metric.ball p r0 :=
      ⟨by rw [← hk]; exact subset_convexHull ℝ _ ⟨k, rfl⟩, Metric.mem_ball_self hr0⟩
    rw [← hS] at hpT
    exact hpT.1
  have hn : 0 < n := pos_of_mem R hpS
  obtain ⟨rT, hrT, hT⟩ := T.volume_inter_ball_localAngle p
  choose ri hri hcontrib using fun i => (R.tile i).volume_inter_ball_localAngle p
  obtain ⟨rc, hrc, hrcle⟩ := exists_common_radius hn ri hri
  set r : ℝ := min (min rT rc) (r0 / 2) with hrdef
  have hrpos : 0 < r := lt_min (lt_min hrT hrc) (by positivity)
  have hr_rT : r ≤ rT := (min_le_left _ _).trans (min_le_left _ _)
  have hr_rc : r ≤ rc := (min_le_left _ _).trans (min_le_right _ _)
  have hr_r0 : r ≤ r0 := (min_le_right _ _).trans (by linarith)
  have hball : Metric.ball p r ⊆ Metric.ball p r0 := Metric.ball_subset_ball hr_r0
  have hSr : S ∩ Metric.ball p r = T.carrier ∩ Metric.ball p r := by
    calc S ∩ Metric.ball p r = (S ∩ Metric.ball p r0) ∩ Metric.ball p r := by
            rw [Set.inter_assoc, Set.inter_eq_self_of_subset_right hball]
      _ = (T.carrier ∩ Metric.ball p r0) ∩ Metric.ball p r := by rw [hS]
      _ = T.carrier ∩ Metric.ball p r := by
            rw [Set.inter_assoc, Set.inter_eq_self_of_subset_right hball]
  have hsum := volume_inter_ball_eq_sum R p r
  rw [hSr, hT r hrpos hr_rT] at hsum
  have htiles : ∀ i ∈ (Finset.univ : Finset (Fin n)),
      volume ((R.tile i).carrier ∩ Metric.ball p r)
        = ENNReal.ofReal ((R.tile i).localAngle p / 2 * r ^ 2) := fun i _ =>
    hcontrib i r hrpos (hr_rc.trans (hrcle i))
  rw [Finset.sum_congr rfl htiles,
    ← ENNReal.ofReal_sum_of_nonneg (fun i _ => by
      have := (R.tile i).localAngle_nonneg p
      positivity)] at hsum
  have hreal := (ENNReal.ofReal_eq_ofReal_iff
    (by have := T.localAngle_nonneg p; positivity)
    (Finset.sum_nonneg fun i _ => by
      have := (R.tile i).localAngle_nonneg p
      positivity)).mp hsum
  have hfact : ∑ i, (R.tile i).localAngle p / 2 * r ^ 2
      = (∑ i, (R.tile i).localAngle p) * (r ^ 2 / 2) := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hfact] at hreal
  have hr2 : (0:ℝ) < r ^ 2 / 2 := by positivity
  have hkey : (∑ i, (R.tile i).localAngle p) * (r ^ 2 / 2) = T.localAngle p * (r ^ 2 / 2) := by
    rw [← hreal]; ring
  rw [← hTp]
  exact mul_right_cancel₀ hr2.ne' hkey

/-- **`prop:fanprune`.**  At a convex corner of angle `W < β ≤ γ` of a region tiled by copies of a
tile with angles `α, β, γ`, every tile's local angle is `α` or `0`, and `W` is `α` times the number
of tiles presenting `α` there. -/
theorem fan_prune_region (R : RTiling S M n) {p : Plane} {W : ℝ} (hc : ConvexCornerAt S p W)
    (α β γ : ℝ)
    (hα : cornerAngle (M.pts 1) (M.pts 0) (M.pts 2) = α)
    (hβ : cornerAngle (M.pts 2) (M.pts 1) (M.pts 0) = β)
    (hγ : cornerAngle (M.pts 0) (M.pts 2) (M.pts 1) = γ)
    (hβγ : β ≤ γ) (hW : W < β) :
    (∀ i, (R.tile i).localAngle p = α ∨ (R.tile i).localAngle p = 0) ∧
    W = ((Finset.univ.filter fun i => (R.tile i).localAngle p = α).card : ℝ) * α := by
  have hsum := sum_localAngle_corner R hc
  have hle : ∀ i, (R.tile i).localAngle p ≤ W := by
    intro i
    rw [← hsum]
    exact Finset.single_le_sum (f := fun i => (R.tile i).localAngle p)
      (fun j _ => (R.tile j).localAngle_nonneg p) (Finset.mem_univ i)
  have hβpi : β ≤ Real.pi := by rw [← hβ]; exact EuclideanGeometry.angle_le_pi _ _ _
  have hcase : ∀ i, (R.tile i).localAngle p = α ∨ (R.tile i).localAngle p = 0 := by
    intro i
    rcases Erdos634.PinPlumbing.localAngle_cases (R.tile i) p with ⟨j, _, hj⟩ | h2 | h1 | h0
    · obtain ⟨m, hm⟩ := congruent_corner_angles (R.cong i).symm j
      have hcases : m = 0 ∨ m = 1 ∨ m = 2 := by fin_cases m <;> simp
      rcases hcases with rfl | rfl | rfl
      · left; rw [hj, hm, ← hα]; congr 1
      · exfalso
        have : (R.tile i).localAngle p = β := by rw [hj, hm, ← hβ]; congr 1
        have := hle i; linarith
      · exfalso
        have : (R.tile i).localAngle p = γ := by rw [hj, hm, ← hγ]; congr 1
        have := hle i; linarith
    · exfalso
      have := hle i
      have := Real.pi_pos
      linarith
    · exfalso
      have := hle i
      linarith
    · exact Or.inr h0
  refine ⟨hcase, ?_⟩
  rw [← hsum]
  have hsplit : ∀ i, (R.tile i).localAngle p
      = if (R.tile i).localAngle p = α then α else 0 := by
    intro i
    rcases hcase i with h | h
    · rw [if_pos h]; exact h
    · by_cases hα0 : (R.tile i).localAngle p = α
      · rw [if_pos hα0]; exact hα0
      · rw [if_neg hα0]; exact h
  rw [Finset.sum_congr rfl (fun i _ => hsplit i), Finset.sum_ite, Finset.sum_const,
    Finset.sum_const_zero, add_zero, nsmul_eq_mul]

/-- **No completion.**  A region with a convex corner of angle `W < β` that is not a natural
multiple of `α` has no tiling by congruent copies of the tile, with any number of tiles. -/
theorem fan_prune_no_completion {p : Plane} {W : ℝ} (hc : ConvexCornerAt S p W)
    (α β γ : ℝ)
    (hα : cornerAngle (M.pts 1) (M.pts 0) (M.pts 2) = α)
    (hβ : cornerAngle (M.pts 2) (M.pts 1) (M.pts 0) = β)
    (hγ : cornerAngle (M.pts 0) (M.pts 2) (M.pts 1) = γ)
    (hβγ : β ≤ γ) (hW : W < β) (hnot : ∀ k : ℕ, W ≠ (k : ℝ) * α) (n : ℕ) :
    IsEmpty (RTiling S M n) :=
  ⟨fun R => hnot _ (fan_prune_region R hc α β γ hα hβ hγ hβγ hW).2⟩

end Erdos634.Draft.FanPruneRegion
