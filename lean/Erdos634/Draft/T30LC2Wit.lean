import Mathlib.Tactic
import Erdos634.Draft.T30LC2Doubled
import Erdos634.Draft.T30LPi3F6CornerWit

/-!
# (C2) at a `π/3` target corner, and its witness on the 1440-tiling

`c2_doubled_corner`: on a `CongruentDissection` with `SixtyData` model, `α ∉ ℚπ`, `a, b, c` pairwise distinct (`a ≠ c`, `b ≠ c`, `a ≠ b` is not needed),
the single-edge word lemma for `c`, at a target corner `k` of angle `π/3` whose adjacent sides are not of length `a` or `b`:
there is a corner tile `T` (`π/3` at the corner) and its two other vertices `P, Q` lie on the two target sides, and on each side the next tile `K` has a `π/3`
vertex at `P` (resp. `Q`) with an edge running on the target side, forward from the corner, of length `a` or `b`: (C2) as a fact about the dissection `D`.
`witness_c2`: every hypothesis is discharged on `G3CSixtyControl.D` (`N = 1440`, tile `(5,8,7)·3360`) at every corner.
-/

namespace Erdos634.C2Forward

open Erdos634.Geometry Erdos634.Pi3Tile Erdos634.Pi3F6 Erdos634.ChordFar Erdos634.Pi3Corner Erdos634.SectorFill

theorem sideTile_ray {N : ℕ} {D : CongruentDissection N} {P u u' : Plane} {a b : ℝ}
    (h : SideTile D P u a b) (hu : u ≠ 0) (hr : SameRay ℝ u' u) : SideTile D P u' a b := by
  obtain ⟨K, l, hl, hang, hray⟩ := h
  refine ⟨K, l, hl, hang, hray.elim (fun ⟨h1, h2⟩ => Or.inl ⟨hr.trans h1 (fun h => absurd h hu), h2⟩)
    (fun ⟨h1, h2⟩ => Or.inr ⟨hr.trans h1 (fun h => absurd h hu), h2⟩)⟩

set_option maxHeartbeats 800000 in
/-- **C2 at a `π/3` target corner.**  See the module header. -/
theorem c2_doubled_corner {N : ℕ} (D : CongruentDissection N) {α a b c : ℝ} (hirr : Irr α)
    (hS : D.model.SixtyData α a b c) (hac : a ≠ c) (hbc : b ≠ c)
    (hword : ∀ x y z : ℕ, (x : ℝ) * a + y * b + z * c = c → x + y + z = 1)
    (k : Fin 3) (hk : D.target.angleAt k = Real.pi / 3)
    (hA1 : dist (D.target.pts k) (D.target.pts (k + 1)) ≠ a)
    (hA2 : dist (D.target.pts k) (D.target.pts (k + 1)) ≠ b)
    (hB1 : dist (D.target.pts k) (D.target.pts (k + 2)) ≠ a)
    (hB2 : dist (D.target.pts k) (D.target.pts (k + 2)) ≠ b) :
    ∃ (i : Fin N) (j : Fin 3), (D.tile i).pts j = D.target.pts k ∧
      ((SideTile D ((D.tile i).pts (j + 1)) (D.target.pts (k + 1) - D.target.pts k) a b ∧
          SideTile D ((D.tile i).pts (j + 2)) (D.target.pts (k + 2) - D.target.pts k) a b) ∨
        (SideTile D ((D.tile i).pts (j + 1)) (D.target.pts (k + 2) - D.target.pts k) a b ∧
          SideTile D ((D.tile i).pts (j + 2)) (D.target.pts (k + 1) - D.target.pts k) a b)) := by
  obtain ⟨i, j, hj, hang, hcase⟩ := Erdos634.Pi3Cone.corner_tile_on_sides D hirr hS k hk
  have hU := tile_sixty D hS i
  have hopp := opp_c_of_pi3 hirr hU j hang
  have hor := tri_two_orient hU hac hbc j hopp
  have e3 : ∀ x : Fin 3, x + 1 + 1 = x + 2 := by decide
  have e4 : ∀ x : Fin 3, x + 2 + 1 = x := by decide
  have e5 : ∀ x : Fin 3, x + 2 + 2 = x + 1 := by decide
  have e6 : ∀ x : Fin 3, x + 1 + 2 = x := by decide
  simp only [Tri.oppLen, e3, e4, e5, e6] at hor
  have hlOQ : dist ((D.tile i).pts (j + 2)) ((D.tile i).pts j) = a ∨ dist ((D.tile i).pts (j + 2)) ((D.tile i).pts j) = b := by
    rcases hor with ⟨h1, -, -, -⟩ | ⟨h1, -, -, -⟩
    · exact Or.inl h1
    · exact Or.inr h1
  have hlOP : dist ((D.tile i).pts j) ((D.tile i).pts (j + 1)) = a ∨ dist ((D.tile i).pts j) ((D.tile i).pts (j + 1)) = b := by
    rcases hor with ⟨-, -, h1, -⟩ | ⟨-, -, h1, -⟩
    · exact Or.inr h1
    · exact Or.inl h1
  have hinj : ∀ m n : Fin 3, m ≠ n → (D.tile i).pts m ≠ (D.tile i).pts n :=
    fun m n h hh => h ((D.tile i).indep.injective hh)
  have hj1 : (D.tile i).pts (j + 1) - D.target.pts k ≠ 0 := by
    rw [sub_ne_zero, ← hj]; exact (hinj _ _ ((by decide : ∀ x : Fin 3, x ≠ x + 1) j)).symm
  have hj2 : (D.tile i).pts (j + 2) - D.target.pts k ≠ 0 := by
    rw [sub_ne_zero, ← hj]; exact (hinj _ _ ((by decide : ∀ x : Fin 3, x ≠ x + 2) j)).symm
  have hAne : D.target.pts (k + 1) - D.target.pts k ≠ 0 := by
    rw [sub_ne_zero]; intro h
    exact (by decide : ∀ x : Fin 3, x + 1 ≠ x) k (D.target.indep.injective h)
  have hBne : D.target.pts (k + 2) - D.target.pts k ≠ 0 := by
    rw [sub_ne_zero]; intro h
    exact (by decide : ∀ x : Fin 3, x + 2 ≠ x) k (D.target.indep.injective h)
  have vk1 : k ≠ k + 1 := (by decide : ∀ x : Fin 3, x ≠ x + 1) k
  have vk2 : k ≠ k + 2 := (by decide : ∀ x : Fin 3, x ≠ x + 2) k
  have v12 : k + 1 ≠ k + 2 := (by decide : ∀ x : Fin 3, x + 1 ≠ x + 2) k
  refine ⟨i, j, hj, ?_⟩
  rcases hcase with ⟨hr1, hr2⟩ | ⟨hr1, hr2⟩
  · obtain ⟨p, hp0, hp⟩ := rayparam hAne hj1 hr1
    obtain ⟨r, hr0, hr⟩ := rayparam hBne hj2 hr2
    have hPA : (D.tile i).pts (j + 1) ≠ D.target.pts (k + 1) := by
      intro h
      rcases hlOP with h' | h'
      · apply hA1; rw [← h', hj, h]
      · apply hA2; rw [← h', hj, h]
    have hQB : (D.tile i).pts (j + 2) ≠ D.target.pts (k + 2) := by
      intro h
      rcases hlOQ with h' | h'
      · apply hB1; rw [← dist_comm, ← h', hj, h]
      · apply hB2; rw [← dist_comm, ← h', hj, h]
    obtain ⟨c1, c2⟩ := c2_config D hirr hS hac hbc hword i j k (k + 1) (k + 2) vk1 vk2 v12 hj hang hp0 hr0
      hp hr hPA hQB
    refine Or.inl ⟨sideTile_ray c1 hj1 ?_, sideTile_ray c2 hj2 ?_⟩
    · rw [hp]; exact SameRay.sameRay_pos_smul_right _ hp0
    · rw [hr]; exact SameRay.sameRay_pos_smul_right _ hr0
  · obtain ⟨p, hp0, hp⟩ := rayparam hBne hj1 hr1
    obtain ⟨r, hr0, hr⟩ := rayparam hAne hj2 hr2
    have hPA : (D.tile i).pts (j + 1) ≠ D.target.pts (k + 2) := by
      intro h
      rcases hlOP with h' | h'
      · apply hB1; rw [← h', hj, h]
      · apply hB2; rw [← h', hj, h]
    have hQB : (D.tile i).pts (j + 2) ≠ D.target.pts (k + 1) := by
      intro h
      rcases hlOQ with h' | h'
      · apply hA1; rw [← dist_comm, ← h', hj, h]
      · apply hA2; rw [← dist_comm, ← h', hj, h]
    obtain ⟨c1, c2⟩ := c2_config D hirr hS hac hbc hword i j k (k + 2) (k + 1) vk2 vk1 v12.symm hj hang hp0 hr0
      hp hr hPA hQB
    refine Or.inr ⟨sideTile_ray c1 hj1 ?_, sideTile_ray c2 hj2 ?_⟩
    · rw [hp]; exact SameRay.sameRay_pos_smul_right _ hp0
    · rw [hr]; exact SameRay.sameRay_pos_smul_right _ hr0

section witness

open Erdos634.Draft.G3CSixtyControl

/-- **WITNESS (real dissection).**  C2 on the certified 1440-tiling: at every corner, on each target side the next tile has a `π/3` vertex with an edge on the
side (length `a = 3360·5` or `b = 3360·8`, never `c`). -/
theorem witness_c2 (k : Fin 3) :
    ∃ i j, (D.tile i).pts j = D.target.pts k ∧
      ((SideTile D ((D.tile i).pts (j + 1)) (D.target.pts (k + 1) - D.target.pts k) (3360 * 5) (3360 * 8) ∧
          SideTile D ((D.tile i).pts (j + 2)) (D.target.pts (k + 2) - D.target.pts k) (3360 * 5) (3360 * 8)) ∨
        (SideTile D ((D.tile i).pts (j + 1)) (D.target.pts (k + 2) - D.target.pts k) (3360 * 5) (3360 * 8) ∧
          SideTile D ((D.tile i).pts (j + 2)) (D.target.pts (k + 1) - D.target.pts k) (3360 * 5) (3360 * 8))) :=
  c2_doubled_corner D (hirr := α_irr) data (by norm_num) (by norm_num) hword_1440 k (t_angle k)
    (by rw [tside]; norm_num) (by rw [tside]; norm_num) (by rw [tside2]; norm_num) (by rw [tside2]; norm_num)

end witness

end Erdos634.C2Forward

#print axioms Erdos634.C2Forward.c2_doubled_corner
#print axioms Erdos634.C2Forward.witness_c2
