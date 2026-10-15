import Mathlib.Tactic
import Erdos634.Draft.T30LL4Wit
import Erdos634.Draft.T30LL4Corner

open scoped Classical

/-!
# Witnesses for the word hypotheses, `word_of_sum_with` and `wall_of_hull_func` on the 1440-tiling

With the swapped model `a = 26880 > b = 16800, c = 23520` (`sixty_swap data`):
* `hword1_wit`, `hwordc_wit`: the two word hypotheses of `l4_corner` hold for the tile `(8,5,7)`; `hword1_fails_835`, `hwordc_fails_347`: they fail for other tiles.
* `word_of_sum_with_wit`: the corner tile's `b`-edge is a one-edge set of total length `b`, and the lemma returns `1 ≤ y`.
* `wall_of_hull_wit`: the open edge `QZ` of the tile `((26880,0),(35280,8400),(8400,8400))` is a wall; `wall_control`: a chord through the tile's interior is not.
All corners of this tiling are of type `(a,b)` (`(26880,26880)`-`(16800,16800)` at all 3 target corners), so `l4_corner`'s own hypotheses (type `(b,a)`) have no witness here.
-/

namespace Erdos634.C2Forward.Wit

open Erdos634.Geometry Erdos634.Draft.G3CCert Erdos634.Draft.G3CAng Erdos634.Draft.G3CSixtyControl Erdos634.CertCoord
open Erdos634.Draft.G3CEqui60n1440 (cert cert_ok)

def t2 : LT := ((26880, 0), (35280, 8400), (8400, 8400))
theorem t2_mem : t2 ∈ cert.leaves := by decide +kernel

theorem tile_pts_of_mem' (t : LT) (ht : t ∈ cert.leaves) :
    ∃ i : Fin cert.leaves.length, ∀ k, (D.tile i).pts k = toPt (vtx t k) := tile_pts_of_mem t ht

theorem hword1_wit : ∀ x y z : ℕ, (x : ℝ) * (3360 * 8) + y * (3360 * 5) + z * (3360 * 7) = 3360 * 8 → y = 0 := by
  intro x y z h
  have h1 : (8 * x + 5 * y + 7 * z : ℝ) = 8 := by linarith
  have h2 : 8 * x + 5 * y + 7 * z = 8 := by exact_mod_cast h1
  omega

theorem hwordc_wit : ∀ x y z : ℕ, (x : ℝ) * (3360 * 8) + y * (3360 * 5) + z * (3360 * 7) = 3360 * 7 → x + y + z = 1 := by
  intro x y z h
  have h1 : (8 * x + 5 * y + 7 * z : ℝ) = 7 := by linarith
  have h2 : 8 * x + 5 * y + 7 * z = 7 := by exact_mod_cast h1
  omega

theorem hword1_fails_835 : ¬ ∀ x y z : ℕ, (x : ℝ) * 8 + y * 3 + z * 5 = 8 → y = 0 := by
  intro h
  have := h 0 1 1 (by norm_num)
  omega

theorem hwordc_fails_347 : ¬ ∀ x y z : ℕ, (x : ℝ) * 3 + y * 4 + z * 7 = 7 → x + y + z = 1 := by
  intro h
  have := h 1 1 0 (by norm_num)
  omega

theorem word_of_sum_with_wit : ∃ x y z : ℕ, 1 ≤ y ∧
    (x : ℝ) * (3360 * 8) + y * (3360 * 5) + z * (3360 * 7) = 3360 * 5 := by
  obtain ⟨i, hp⟩ := tile_pts_of_mem' t0 t0_mem
  have hS := sixty_swap data
  have hlen : dist ((D.tile i).pts 2) ((D.tile i).pts (2 + 1)) = 3360 * 5 := by
    rw [hp, show (2 : Fin 3) + 1 = 0 from rfl, hp]
    have := dist_toPt_nat (vtx t0 2) (vtx t0 0) 16800 (by decide)
    rw [this]; norm_num
  refine word_of_sum_with D hS (by norm_num) (by norm_num) (by norm_num) {(i, 2)} (3360 * 5) (by norm_num) ?_
    (i, 2) (Finset.mem_singleton_self _) hlen
  rw [Finset.sum_singleton]
  show ENNReal.ofReal (dist ((D.tile i).pts 2) ((D.tile i).pts (2 + 1))) = _
  rw [hlen]

theorem wall_of_hull_wit : ∃ P Q Z : Plane, P ≠ Q ∧ ∀ y ∈ openSegment ℝ Q Z, ∀ i, y ∉ interior (D.tile i).carrier := by
  have h3 := s3pos
  obtain ⟨j, hp⟩ := tile_pts_of_mem' t2 t2_mem
  have hcar : (D.tile j).carrier = convexHull ℝ {toPt (26880, 0), toPt (35280, 8400), toPt (8400, 8400)} := by
    show convexHull ℝ (Set.range (D.tile j).pts) = _
    congr 1
    ext x
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨k, rfl⟩
      rw [hp]
      fin_cases k <;> simp [t2, vtx]
    · rintro (rfl | rfl | rfl)
      · exact ⟨0, by rw [hp]; rfl⟩
      · exact ⟨1, by rw [hp]; rfl⟩
      · exact ⟨2, by rw [hp]; rfl⟩
  refine ⟨toPt (26880, 0), toPt (35280, 8400), toPt (8400, 8400), ?_, ?_⟩
  · intro h
    have := congrArg (fun x : Plane => x 0) h
    simp only [toPt_0] at this
    norm_num at this
  · refine wall_of_hull_func D.toDissection j hcar (-fY) (neg_ne_zero.mpr fY_ne) (-(fY (toPt (35280, 8400)))) ?_ ?_ ?_
    · simp
    · simp only [LinearMap.neg_apply, fY_toPt]
    · simp only [LinearMap.neg_apply, fY_toPt]; push_cast; nlinarith

theorem wall_control : ∃ y ∈ openSegment ℝ (toPt (35280, 8400))
    ((1 / 2 : ℝ) • toPt (26880, 0) + (1 / 2 : ℝ) • toPt (8400, 8400)), ∃ i, y ∈ interior (D.tile i).carrier := by
  obtain ⟨j, hp⟩ := tile_pts_of_mem' t2 t2_mem
  have := interior_of_three (D.tile j) 0 (1 / 4) (1 / 2) (1 / 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨_, ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, rfl⟩, j, ?_⟩
  convert this using 1
  rw [show (0 : Fin 3) + 1 = 1 from rfl, show (0 : Fin 3) + 2 = 2 from rfl, hp, hp, hp]
  simp only [t2, vtx, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons]
  module

end Erdos634.C2Forward.Wit

#print axioms Erdos634.C2Forward.Wit.word_of_sum_with_wit
#print axioms Erdos634.C2Forward.Wit.wall_of_hull_wit
#print axioms Erdos634.C2Forward.Wit.wall_control
#print axioms Erdos634.C2Forward.Wit.hword1_wit
