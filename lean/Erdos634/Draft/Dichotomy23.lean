import Erdos634.Refl.MPG23Sound
import Erdos634.Draft.GapE120Dis

/-!
# The unit parallelogram of the member `(e,f) = (2,3)` admits no tiling

The unit parallelogram of the member `(e,f) = (2,3)`, with sides `Y₁ = 46` and
`X₁ = 27` with angle `β`, tile `(6,5,9)`, 46 tiles, admits no tiling.

`pgram23` is that parallelogram in coordinates: `cos β = 23/27`, `sin β = 10√2/27`, so its vertices are
`(0,0), (46,0), (69, 10√2), (23, 10√2)`.  `dichotomy_23`: no `CongruentRegionDissection` (any number of tiles, isometries
including reflections) has region `pgram23` and a tile with sides `6, 5, 9`.

Certificate: `Refl.MPG23.not_region_dissection` (3,151 nodes, free-branch-point checker for polygon targets,
`Refl.checkNodeP_sound`).  No sorry, no native_decide.
-/

open Erdos634.CertNode Erdos634.Geometry Erdos634.CertCoord

namespace Erdos634.Draft.Dichotomy23

open Refl

/-- the parallelogram with sides `46` (along the `x`-axis) and `27` at angle `β`, `cos β = 23/27` -/
def pgram23 : Set Plane :=
  {p | ∃ s t : ℝ, 0 ≤ s ∧ s ≤ 1 ∧ 0 ≤ t ∧ t ≤ 1 ∧ p = mkPt (46 * s + 23 * t) (10 * Real.sqrt 2 * t)}

theorem h2 : (0 : ℝ) < 2 := by norm_num

/-- the four side lengths and the angle: the vertices are at distances `46`, `27` -/
theorem pgram23_sides :
    dist (mkPt 0 0) (mkPt 46 0) = 46 ∧ dist (mkPt 0 0) (mkPt 23 (10 * Real.sqrt 2)) = 27 := by
  have hs : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  constructor
  · rw [show (46 : ℝ) = Real.sqrt (46 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    rw [EuclideanSpace.dist_eq]; congr 1
    simp [Fin.sum_univ_two, mkPt_zero, mkPt_one]
  · rw [show (27 : ℝ) = Real.sqrt (27 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    rw [EuclideanSpace.dist_eq]; congr 1
    simp only [Fin.sum_univ_two, mkPt_zero, mkPt_one, Real.dist_eq]
    rw [sq_abs, sq_abs]
    nlinarith [hs]

theorem e0 (X Y : ℝ) : evalL (MPG23.inst.tgt.edge 0) X Y = 184 * Y := by
  simp [MPG23.inst, _root_.Tri.edge, _root_.Tri.vert, linOf, evalL, pt]
theorem e1 (X Y : ℝ) : evalL (MPG23.inst.tgt.edge 1) X Y = -40 * X - 92 * Y + 7360 := by
  simp [MPG23.inst, _root_.Tri.edge, _root_.Tri.vert, linOf, evalL, pt]; ring
theorem e2 (X Y : ℝ) : evalL (MPG23.inst.tgt.edge 2) X Y = 40 * X - 92 * Y := by
  simp [MPG23.inst, _root_.Tri.edge, _root_.Tri.vert, linOf, evalL, pt]; ring

theorem tgt_ok : MPG23.inst.tgt.ok = true := by decide +kernel

/-- the checker's region is the parallelogram -/
theorem region_eq : MPG23.inst.tgt.carr 2 ∩ extSet 2 MPG23.ext = pgram23 := by
  have hsr : (0 : ℝ) < sr 2 := sr_pos h2
  ext p
  obtain ⟨X, Y, rfl⟩ := exists_rp h2 p
  constructor
  · rintro ⟨hT, hE⟩
    have a0 := Tri.edge_nonneg 2 h2 MPG23.inst.tgt tgt_ok X Y hT 0 (by norm_num)
    have a2 := Tri.edge_nonneg 2 h2 MPG23.inst.tgt tgt_ok X Y hT 2 (by norm_num)
    rw [e0] at a0; rw [e2] at a2
    have x1 := (mem_halfL_rp 2 h2 _ X Y).mp (hE ⟨-10, 23, 460⟩ (by simp [MPG23.ext]))
    have x2 := (mem_halfL_rp 2 h2 _ X Y).mp (hE ⟨0, -46, 460⟩ (by simp [MPG23.ext]))
    simp only [evalL] at x1 x2
    push_cast at x1 x2
    refine ⟨(10 * X - 23 * Y) / 460, Y / 10, ?_, ?_, ?_, ?_, ?_⟩
    · apply div_nonneg <;> linarith
    · rw [div_le_one (by norm_num)]; linarith
    · apply div_nonneg <;> linarith
    · rw [div_le_one (by norm_num)]; linarith
    · unfold rp sr
      congr 1
      · ring
      · ring
  · rintro ⟨s, t, hs0, hs1, ht0, ht1, hp⟩
    have hXY : rp 2 X Y = rp 2 (46 * s + 23 * t) (10 * t) := by
      rw [hp]; unfold rp sr; congr 1; ring
    rw [hXY]
    refine ⟨Tri.mem_of_edges 2 h2 _ tgt_ok _ _ ?_, ?_⟩
    · intro i hi
      interval_cases i
      · rw [e0]; nlinarith
      · rw [e1]; nlinarith
      · rw [e2]; nlinarith
    · intro l hl
      refine (mem_halfL_rp 2 h2 l _ _).mpr ?_
      simp only [MPG23.ext, List.mem_cons, List.mem_nil_iff, or_false] at hl
      rcases hl with rfl | rfl
      · simp only [evalL]; push_cast; nlinarith
      · simp only [evalL]; push_cast; nlinarith

open Erdos634.Geometry.GapE120Dis in
/-- **`thm:dichotomy`**: the unit parallelogram of `(e,f) = (2,3)` admits no tiling by the tile `(6,5,9)`. -/
theorem dichotomy_23 {N : ℕ} (D : Erdos634.RegionDissection.CongruentRegionDissection N)
    (hR : D.region = pgram23)
    (hM : ∃ σ : Equiv.Perm (Fin 3), D.model.oppLen (σ 0) = 6 ∧ D.model.oppLen (σ 1) = 5 ∧
      D.model.oppLen (σ 2) = 9) : False := by
  obtain ⟨σ, m0, m1, m2⟩ := hM
  obtain ⟨s1, s2, s3⟩ := sides_of_perm D.model σ
  rw [m0] at s1; rw [m1] at s2; rw [m2] at s3
  obtain ⟨k1, k2, k3⟩ := MPG23.MODEL_sides
  have hMc : D.model.Congruent MPG23.MODEL := by
    set ρ : Equiv.Perm (Fin 3) := (finRotate 3).trans σ with hρ
    have h0' : ρ 0 = σ 1 := by simp [hρ, fr0]
    have h1' : ρ 1 = σ 2 := by simp [hρ, fr1]
    have h2' : ρ 2 = σ 0 := by simp [hρ, fr2]
    have hc := Tri.congruent_of_dist (D.model.relabel ρ) MPG23.MODEL
      (by simp only [Tri.relabel_pts, Function.comp]; rw [h0', h1', s1, k1])
      (by simp only [Tri.relabel_pts, Function.comp]; rw [h1', h2', dist_comm, s2, k2])
      (by simp only [Tri.relabel_pts, Function.comp]; rw [h0', h2', dist_comm, s3, k3])
    exact (D.model.congruent_relabel ρ).trans hc
  exact MPG23.not_region_dissection D (by rw [hR, region_eq]) hMc

end Erdos634.Draft.Dichotomy23

#print axioms Erdos634.Draft.Dichotomy23.dichotomy_23
