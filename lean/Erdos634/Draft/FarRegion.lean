/-
Draft/FarRegion.lean -- the far region is the scaled tile.

Tile `(a, b, c) = (ef, f² − e², f²)`; target `Δ_m` with base `m e (3f² − e²)` and legs `m f³`.  The cevian from the
apex to the base point `Q` at distance `f m a` from a base corner cuts off the corner triangle
`CevianAtomFull.WestT` (corner, `Q`, apex).

* `far_sides` (`CevianAtomFull.WestT_sides`): its sides are `f m a` (on the base), `f m b` (the cevian) and
  `f m c` (on the leg): the tile scaled by `f m`.
* `far_congruent`: the standard subdivision `WtoDeltaF.ladderCD` of the tile scaled by `f m`, into `(f m)²` copies,
  has a target congruent to it.  So the far region has a tiling.
* `far_area`: its area is `(f m)²` times the area of the tile.
* `ladder_side_AC`, `far_ray_side`, `far_ray_edge`: in that subdivision the side of length `f m b` is made of
  `f m` tile edges of length `b`, end to end from the vertex: the ray side reads `b^(f m)`, with junctions at the
  multiples of `b`.

Plane geometry and an explicit tiling; nothing here assumes a tiling of the target.  No sorry, no native_decide.
-/
import Erdos634.Draft.CevianAtomFull

open scoped Classical

namespace Erdos634.Draft.FarRegion

open Erdos634.Geometry Erdos634.Subdivision
open Erdos634.Draft.WideColFull Erdos634.Draft.AddLawFull Erdos634.Draft.CevianAtomFull

/-- in the standard subdivision of a triangle scaled by `k` about `A`, the side from `A` towards `C` is made of
`k` cells' edges, the `j`-th from `A + j (C − A)` to `A + (j + 1)(C − A)` -/
theorem ladder_side_AC (A B C : Plane) (hindep : AffineIndependent ℝ ![A, B, C]) (k : ℕ) (hk : 0 < k)
    (j : ℕ) (hj : j < k) :
    ∃ n : Fin (k * k),
      ((ladderDissection A B C hindep k hk).tile n).pts 0 = A + (j : ℝ) • (C - A) ∧
      ((ladderDissection A B C hindep k hk).tile n).pts 2 = A + ((j : ℝ) + 1) • (C - A) := by
  have hmem : ((true, (0, j)) : Bool × ℕ × ℕ) ∈ cellSet k := by
    unfold cellSet
    exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨(0, j), mem_upSet.mpr (by omega), rfl⟩)
  refine ⟨(cellIdx k).symm ⟨_, hmem⟩, ?_, ?_⟩
  · show (cellOf A B C hindep ((cellIdx k ((cellIdx k).symm ⟨_, hmem⟩) : Bool × ℕ × ℕ))).pts 0 = _
    rw [Equiv.apply_symm_apply]
    simp [cellOf, cellUp, P]
  · show (cellOf A B C hindep ((cellIdx k ((cellIdx k).symm ⟨_, hmem⟩) : Bool × ℕ × ℕ))).pts 2 = _
    rw [Equiv.apply_symm_apply]
    simp [cellOf, cellUp, P]

variable (e f m : ℕ) (he : 1 ≤ e) (hef : e < f) (hm : 1 ≤ m)

/-- **The far region has the sides of the tile scaled by `f m`**: `f m a` on the base, `f m b` along the cevian,
`f m c` on the leg. -/
theorem far_sides :
    dist ((WestT (e : ℝ) (f : ℝ) (m : ℝ) (Nat.cast_pos.2 he) (Nat.cast_lt.2 hef) (Nat.cast_pos.2 hm)).pts 0)
        ((WestT (e : ℝ) (f : ℝ) (m : ℝ) (Nat.cast_pos.2 he) (Nat.cast_lt.2 hef) (Nat.cast_pos.2 hm)).pts 1)
      = (m : ℝ) * ((e : ℝ) * (f : ℝ) ^ 2) ∧
    dist ((WestT (e : ℝ) (f : ℝ) (m : ℝ) (Nat.cast_pos.2 he) (Nat.cast_lt.2 hef) (Nat.cast_pos.2 hm)).pts 1)
        ((WestT (e : ℝ) (f : ℝ) (m : ℝ) (Nat.cast_pos.2 he) (Nat.cast_lt.2 hef) (Nat.cast_pos.2 hm)).pts 2)
      = (m : ℝ) * ((f : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)) ∧
    dist ((WestT (e : ℝ) (f : ℝ) (m : ℝ) (Nat.cast_pos.2 he) (Nat.cast_lt.2 hef) (Nat.cast_pos.2 hm)).pts 2)
        ((WestT (e : ℝ) (f : ℝ) (m : ℝ) (Nat.cast_pos.2 he) (Nat.cast_lt.2 hef) (Nat.cast_pos.2 hm)).pts 0)
      = (m : ℝ) * (f : ℝ) ^ 3 :=
  WestT_sides _ _ _

/-- **The far region is tiled**: the standard subdivision of the tile scaled by `f m` into `(f m)²` copies has a
target congruent to the far region. -/
theorem far_congruent (hK : 0 < f * m) :
    ((WtoDeltaF.ladderCD (MTn e f he hef) (f * m) hK).target).Congruent
      (WestT (e : ℝ) (f : ℝ) (m : ℝ) (Nat.cast_pos.2 he) (Nat.cast_lt.2 hef) (Nat.cast_pos.2 hm)) := by
  have heR : (0 : ℝ) < (e : ℝ) := Nat.cast_pos.2 he
  have hefR : (e : ℝ) < (f : ℝ) := Nat.cast_lt.2 hef
  have hmR : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.2 hm
  obtain ⟨s1, s2, s3⟩ := MTn_sides e f he hef
  obtain ⟨w1, w2, w3⟩ := WestT_sides heR hefR hmR
  have tg : (WtoDeltaF.ladderCD (MTn e f he hef) (f * m) hK).target
      = Erdos634.Subdivision.bigTri _ _ _ (WtoDeltaF.indep_eta (MTn e f he hef)) (f * m) hK := rfl
  have l01 : dist ((WtoDeltaF.ladderCD (MTn e f he hef) (f * m) hK).target.pts 0)
      ((WtoDeltaF.ladderCD (MTn e f he hef) (f * m) hK).target.pts 1)
      = (m : ℝ) * ((e : ℝ) * (f : ℝ) ^ 2) := by
    rw [tg, WtoDeltaF.big_d01, s1]
    push_cast
    ring
  have l12 : dist ((WtoDeltaF.ladderCD (MTn e f he hef) (f * m) hK).target.pts 1)
      ((WtoDeltaF.ladderCD (MTn e f he hef) (f * m) hK).target.pts 2) = (m : ℝ) * (f : ℝ) ^ 3 := by
    rw [tg, WtoDeltaF.big_d12, s2]
    push_cast
    ring
  have l20 : dist ((WtoDeltaF.ladderCD (MTn e f he hef) (f * m) hK).target.pts 2)
      ((WtoDeltaF.ladderCD (MTn e f he hef) (f * m) hK).target.pts 0)
      = (m : ℝ) * ((f : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)) := by
    rw [tg, WtoDeltaF.big_d20, s3]
    push_cast
    ring
  exact cong_swap01 (by rw [l01, dist_comm, w1]) (by rw [l12, dist_comm, w3]) (by rw [l20, dist_comm, w2])

/-- **The far region has `(f m)²` times the area of the tile.** -/
theorem far_area (hK : 0 < f * m) :
    MeasureTheory.volume
        (WestT (e : ℝ) (f : ℝ) (m : ℝ) (Nat.cast_pos.2 he) (Nat.cast_lt.2 hef) (Nat.cast_pos.2 hm)).carrier
      = ((f * m * (f * m) : ℕ) : ENNReal) * MeasureTheory.volume (MTn e f he hef).carrier := by
  rw [← Erdos634.CongruentArea.volume_congruent (far_congruent e f m he hef hm hK)]
  exact Erdos634.CongruentArea.congruentDissection_volume_target
    (WtoDeltaF.ladderCD (MTn e f he hef) (f * m) hK)

/-- **The ray side reads `b^(f m)`**: the side of the subdivision corresponding to the cevian is made of `f m`
tile edges, the `j`-th from `A + j (C − A)` to `A + (j + 1)(C − A)`, where `A`, `C` are the ends of the `b`-edge
of the tile. -/
theorem far_ray_side (hK : 0 < f * m) (j : ℕ) (hj : j < f * m) :
    ∃ n : Fin (f * m * (f * m)),
      ((WtoDeltaF.ladderCD (MTn e f he hef) (f * m) hK).tile n).pts 0
        = (MTn e f he hef).pts 0 + (j : ℝ) • ((MTn e f he hef).pts 2 - (MTn e f he hef).pts 0) ∧
      ((WtoDeltaF.ladderCD (MTn e f he hef) (f * m) hK).tile n).pts 2
        = (MTn e f he hef).pts 0 + ((j : ℝ) + 1) • ((MTn e f he hef).pts 2 - (MTn e f he hef).pts 0) :=
  ladder_side_AC _ _ _ (WtoDeltaF.indep_eta (MTn e f he hef)) (f * m) hK j hj

/-- each of those edges has length `b = f² − e²` -/
theorem far_ray_edge (j : ℕ) :
    dist ((MTn e f he hef).pts 0 + (j : ℝ) • ((MTn e f he hef).pts 2 - (MTn e f he hef).pts 0))
      ((MTn e f he hef).pts 0 + ((j : ℝ) + 1) • ((MTn e f he hef).pts 2 - (MTn e f he hef).pts 0))
      = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
  obtain ⟨-, -, s3⟩ := MTn_sides e f he hef
  rw [dist_eq_norm]
  have h : (MTn e f he hef).pts 0 + (j : ℝ) • ((MTn e f he hef).pts 2 - (MTn e f he hef).pts 0)
      - ((MTn e f he hef).pts 0 + ((j : ℝ) + 1) • ((MTn e f he hef).pts 2 - (MTn e f he hef).pts 0))
      = (MTn e f he hef).pts 0 - (MTn e f he hef).pts 2 := by module
  rw [h, ← dist_eq_norm, dist_comm]
  exact s3

end Erdos634.Draft.FarRegion

#print axioms Erdos634.Draft.FarRegion.far_congruent
#print axioms Erdos634.Draft.FarRegion.far_ray_side
