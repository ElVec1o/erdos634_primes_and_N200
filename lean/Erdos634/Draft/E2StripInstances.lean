import Erdos634.Refl.MSTR23w4Sound
import Erdos634.Refl.MSTR23w10Sound
import Erdos634.Refl.MSTR23w16Sound
import Erdos634.Refl.MSTR23w22Sound
import Erdos634.Refl.MSTR34w21Sound
import Erdos634.Draft.HasSidesPerm

/-!
# The searched instances of the brick-interior obstruction: five strips with no dissection at all

Exhaustive search finds that no interior of any kind exists in the cases tested:
on `(2,3)` the widths `s = 4, 10, 16, 22`, and on `(3,4)` the width `s = 21`.

The strip of the member `(e,f)` with width `s` is the parallelogram spanned by `s·u` (`u` horizontal) and a slant of
length `f·b` at the angle `α+β`, `cos(α+β) = e/(2f)`.  For `(2,3)` (tile `(6,5,9)`): slant `(5, 10√2)`, length 15.
For `(3,4)` (tile `(12,7,16)`): slant `(21/2, (7/2)√55)`, length 28.  Each theorem: no `CongruentRegionDissection`
(any number of tiles, reflections allowed) of that strip by the tile.

Certificates: `Refl.MSTR23w{4,10,16,22}`, `Refl.MSTR34w21` (1, 13, 79, 184, 17 nodes; polygon checker
`Refl.checkNodeP_sound`).  This module covers only these five instances; the general brick-interior statement
(de Bruijn--Klarner bridge) is in `E2StripFull`.  No sorry, no native_decide.
-/

open Erdos634.CertNode Erdos634.Geometry Erdos634.CertCoord

namespace Erdos634.Draft.E2StripInstances

open Refl Erdos634.Draft.FDBBaseBetaE1

/-- the parallelogram spanned by `(s, 0)` and `(vx, vy)` -/
def strip (s vx vy : ℝ) : Set Plane :=
  {p | ∃ σ τ : ℝ, 0 ≤ σ ∧ σ ≤ 1 ∧ 0 ≤ τ ∧ τ ≤ 1 ∧ p = mkPt (s * σ + vx * τ) (vy * τ)}

/-! ## `STR23w4`: width 4, tile (6,5,9) -/

namespace WSTR23w4

theorem hD : (0 : ℝ) < 2 := by norm_num
theorem e0 (X Y : ℝ) : evalL (Refl.MSTR23w4.inst.tgt.edge 0) X Y = 16 * Y := by
  first
    | (simp [Refl.MSTR23w4.inst, _root_.Tri.edge, _root_.Tri.vert, linOf, evalL, pt]; done)
    | (simp [Refl.MSTR23w4.inst, _root_.Tri.edge, _root_.Tri.vert, linOf, evalL, pt]; ring)
theorem e1 (X Y : ℝ) : evalL (Refl.MSTR23w4.inst.tgt.edge 1) X Y = -40 * X + 4 * Y + 640 := by
  first
    | (simp [Refl.MSTR23w4.inst, _root_.Tri.edge, _root_.Tri.vert, linOf, evalL, pt]; done)
    | (simp [Refl.MSTR23w4.inst, _root_.Tri.edge, _root_.Tri.vert, linOf, evalL, pt]; ring)
theorem e2 (X Y : ℝ) : evalL (Refl.MSTR23w4.inst.tgt.edge 2) X Y = 40 * X - 20 * Y := by
  first
    | (simp [Refl.MSTR23w4.inst, _root_.Tri.edge, _root_.Tri.vert, linOf, evalL, pt]; done)
    | (simp [Refl.MSTR23w4.inst, _root_.Tri.edge, _root_.Tri.vert, linOf, evalL, pt]; ring)
theorem tgt_ok : Refl.MSTR23w4.inst.tgt.ok = true := by decide +kernel

theorem region_eq : Refl.MSTR23w4.inst.tgt.carr 2 ∩ extSet 2 Refl.MSTR23w4.ext = strip 4 5 (10 * Real.sqrt 2) := by
  ext p
  obtain ⟨X, Y, rfl⟩ := exists_rp hD p
  constructor
  · rintro ⟨hT, hE⟩
    have a0 := Tri.edge_nonneg 2 hD Refl.MSTR23w4.inst.tgt tgt_ok X Y hT 0 (by norm_num)
    have a2 := Tri.edge_nonneg 2 hD Refl.MSTR23w4.inst.tgt tgt_ok X Y hT 2 (by norm_num)
    rw [e0] at a0; rw [e2] at a2
    have x1 := (mem_halfL_rp 2 hD _ X Y).mp (hE ⟨-10, 5, 40⟩ (by simp [Refl.MSTR23w4.ext]))
    have x2 := (mem_halfL_rp 2 hD _ X Y).mp (hE ⟨0, -4, 40⟩ (by simp [Refl.MSTR23w4.ext]))
    simp only [evalL] at x1 x2
    push_cast at x1 x2
    refine ⟨(40 * X - 20 * Y) / 160, Y / 10, ?_, ?_, ?_, ?_, ?_⟩
    · apply div_nonneg <;> linarith
    · rw [div_le_one (by norm_num)]; linarith
    · apply div_nonneg <;> linarith
    · rw [div_le_one (by norm_num)]; linarith
    · unfold rp sr
      congr 1
      · ring
      · ring
  · rintro ⟨σ, τ, hs0, hs1, ht0, ht1, hp⟩
    have hXY : rp 2 X Y = rp 2 (4 * σ + 5 * τ) (10 * τ) := by
      rw [hp]; unfold rp sr; congr 1; ring
    rw [hXY]
    refine ⟨Tri.mem_of_edges 2 hD _ tgt_ok _ _ ?_, ?_⟩
    · intro i hi
      interval_cases i
      · rw [e0]; nlinarith
      · rw [e1]; nlinarith
      · rw [e2]; nlinarith
    · intro l hl
      refine (mem_halfL_rp 2 hD l _ _).mpr ?_
      simp only [Refl.MSTR23w4.ext, List.mem_cons, List.mem_nil_iff, or_false] at hl
      rcases hl with rfl | rfl
      · simp only [evalL]; push_cast; nlinarith
      · simp only [evalL]; push_cast; nlinarith

/-- the strip of width 4 has no dissection by the tile `(6,5,9)` -/
theorem no_dissection {N : ℕ} (D : Erdos634.RegionDissection.CongruentRegionDissection N)
    (hR : D.region = strip 4 5 (10 * Real.sqrt 2)) (hM : HasSides D.model 6 5 9) : False := by
  obtain ⟨k1, k2, k3⟩ := Refl.MSTR23w4.MODEL_sides
  exact Refl.MSTR23w4.not_region_dissection D (by rw [hR, region_eq]) (congruent_of_hasSides' (hasSides_rot hM) k1 k2 k3)

end WSTR23w4

/-! ## `STR23w10`: width 10, tile (6,5,9) -/

namespace WSTR23w10

theorem hD : (0 : ℝ) < 2 := by norm_num
theorem e0 (X Y : ℝ) : evalL (Refl.MSTR23w10.inst.tgt.edge 0) X Y = 40 * Y := by
  first
    | (simp [Refl.MSTR23w10.inst, _root_.Tri.edge, _root_.Tri.vert, linOf, evalL, pt]; done)
    | (simp [Refl.MSTR23w10.inst, _root_.Tri.edge, _root_.Tri.vert, linOf, evalL, pt]; ring)
theorem e1 (X Y : ℝ) : evalL (Refl.MSTR23w10.inst.tgt.edge 1) X Y = -40 * X - 20 * Y + 1600 := by
  first
    | (simp [Refl.MSTR23w10.inst, _root_.Tri.edge, _root_.Tri.vert, linOf, evalL, pt]; done)
    | (simp [Refl.MSTR23w10.inst, _root_.Tri.edge, _root_.Tri.vert, linOf, evalL, pt]; ring)
theorem e2 (X Y : ℝ) : evalL (Refl.MSTR23w10.inst.tgt.edge 2) X Y = 40 * X - 20 * Y := by
  first
    | (simp [Refl.MSTR23w10.inst, _root_.Tri.edge, _root_.Tri.vert, linOf, evalL, pt]; done)
    | (simp [Refl.MSTR23w10.inst, _root_.Tri.edge, _root_.Tri.vert, linOf, evalL, pt]; ring)
theorem tgt_ok : Refl.MSTR23w10.inst.tgt.ok = true := by decide +kernel

theorem region_eq : Refl.MSTR23w10.inst.tgt.carr 2 ∩ extSet 2 Refl.MSTR23w10.ext = strip 10 5 (10 * Real.sqrt 2) := by
  ext p
  obtain ⟨X, Y, rfl⟩ := exists_rp hD p
  constructor
  · rintro ⟨hT, hE⟩
    have a0 := Tri.edge_nonneg 2 hD Refl.MSTR23w10.inst.tgt tgt_ok X Y hT 0 (by norm_num)
    have a2 := Tri.edge_nonneg 2 hD Refl.MSTR23w10.inst.tgt tgt_ok X Y hT 2 (by norm_num)
    rw [e0] at a0; rw [e2] at a2
    have x1 := (mem_halfL_rp 2 hD _ X Y).mp (hE ⟨-10, 5, 100⟩ (by simp [Refl.MSTR23w10.ext]))
    have x2 := (mem_halfL_rp 2 hD _ X Y).mp (hE ⟨0, -10, 100⟩ (by simp [Refl.MSTR23w10.ext]))
    simp only [evalL] at x1 x2
    push_cast at x1 x2
    refine ⟨(40 * X - 20 * Y) / 400, Y / 10, ?_, ?_, ?_, ?_, ?_⟩
    · apply div_nonneg <;> linarith
    · rw [div_le_one (by norm_num)]; linarith
    · apply div_nonneg <;> linarith
    · rw [div_le_one (by norm_num)]; linarith
    · unfold rp sr
      congr 1
      · ring
      · ring
  · rintro ⟨σ, τ, hs0, hs1, ht0, ht1, hp⟩
    have hXY : rp 2 X Y = rp 2 (10 * σ + 5 * τ) (10 * τ) := by
      rw [hp]; unfold rp sr; congr 1; ring
    rw [hXY]
    refine ⟨Tri.mem_of_edges 2 hD _ tgt_ok _ _ ?_, ?_⟩
    · intro i hi
      interval_cases i
      · rw [e0]; nlinarith
      · rw [e1]; nlinarith
      · rw [e2]; nlinarith
    · intro l hl
      refine (mem_halfL_rp 2 hD l _ _).mpr ?_
      simp only [Refl.MSTR23w10.ext, List.mem_cons, List.mem_nil_iff, or_false] at hl
      rcases hl with rfl | rfl
      · simp only [evalL]; push_cast; nlinarith
      · simp only [evalL]; push_cast; nlinarith

/-- the strip of width 10 has no dissection by the tile `(6,5,9)` -/
theorem no_dissection {N : ℕ} (D : Erdos634.RegionDissection.CongruentRegionDissection N)
    (hR : D.region = strip 10 5 (10 * Real.sqrt 2)) (hM : HasSides D.model 6 5 9) : False := by
  obtain ⟨k1, k2, k3⟩ := Refl.MSTR23w10.MODEL_sides
  exact Refl.MSTR23w10.not_region_dissection D (by rw [hR, region_eq]) (congruent_of_hasSides' (hasSides_rot hM) k1 k2 k3)

end WSTR23w10

/-! ## `STR23w16`: width 16, tile (6,5,9) -/

namespace WSTR23w16

theorem hD : (0 : ℝ) < 2 := by norm_num
theorem e0 (X Y : ℝ) : evalL (Refl.MSTR23w16.inst.tgt.edge 0) X Y = 64 * Y := by
  first
    | (simp [Refl.MSTR23w16.inst, _root_.Tri.edge, _root_.Tri.vert, linOf, evalL, pt]; done)
    | (simp [Refl.MSTR23w16.inst, _root_.Tri.edge, _root_.Tri.vert, linOf, evalL, pt]; ring)
theorem e1 (X Y : ℝ) : evalL (Refl.MSTR23w16.inst.tgt.edge 1) X Y = -40 * X - 44 * Y + 2560 := by
  first
    | (simp [Refl.MSTR23w16.inst, _root_.Tri.edge, _root_.Tri.vert, linOf, evalL, pt]; done)
    | (simp [Refl.MSTR23w16.inst, _root_.Tri.edge, _root_.Tri.vert, linOf, evalL, pt]; ring)
theorem e2 (X Y : ℝ) : evalL (Refl.MSTR23w16.inst.tgt.edge 2) X Y = 40 * X - 20 * Y := by
  first
    | (simp [Refl.MSTR23w16.inst, _root_.Tri.edge, _root_.Tri.vert, linOf, evalL, pt]; done)
    | (simp [Refl.MSTR23w16.inst, _root_.Tri.edge, _root_.Tri.vert, linOf, evalL, pt]; ring)
theorem tgt_ok : Refl.MSTR23w16.inst.tgt.ok = true := by decide +kernel

theorem region_eq : Refl.MSTR23w16.inst.tgt.carr 2 ∩ extSet 2 Refl.MSTR23w16.ext = strip 16 5 (10 * Real.sqrt 2) := by
  ext p
  obtain ⟨X, Y, rfl⟩ := exists_rp hD p
  constructor
  · rintro ⟨hT, hE⟩
    have a0 := Tri.edge_nonneg 2 hD Refl.MSTR23w16.inst.tgt tgt_ok X Y hT 0 (by norm_num)
    have a2 := Tri.edge_nonneg 2 hD Refl.MSTR23w16.inst.tgt tgt_ok X Y hT 2 (by norm_num)
    rw [e0] at a0; rw [e2] at a2
    have x1 := (mem_halfL_rp 2 hD _ X Y).mp (hE ⟨-10, 5, 160⟩ (by simp [Refl.MSTR23w16.ext]))
    have x2 := (mem_halfL_rp 2 hD _ X Y).mp (hE ⟨0, -16, 160⟩ (by simp [Refl.MSTR23w16.ext]))
    simp only [evalL] at x1 x2
    push_cast at x1 x2
    refine ⟨(40 * X - 20 * Y) / 640, Y / 10, ?_, ?_, ?_, ?_, ?_⟩
    · apply div_nonneg <;> linarith
    · rw [div_le_one (by norm_num)]; linarith
    · apply div_nonneg <;> linarith
    · rw [div_le_one (by norm_num)]; linarith
    · unfold rp sr
      congr 1
      · ring
      · ring
  · rintro ⟨σ, τ, hs0, hs1, ht0, ht1, hp⟩
    have hXY : rp 2 X Y = rp 2 (16 * σ + 5 * τ) (10 * τ) := by
      rw [hp]; unfold rp sr; congr 1; ring
    rw [hXY]
    refine ⟨Tri.mem_of_edges 2 hD _ tgt_ok _ _ ?_, ?_⟩
    · intro i hi
      interval_cases i
      · rw [e0]; nlinarith
      · rw [e1]; nlinarith
      · rw [e2]; nlinarith
    · intro l hl
      refine (mem_halfL_rp 2 hD l _ _).mpr ?_
      simp only [Refl.MSTR23w16.ext, List.mem_cons, List.mem_nil_iff, or_false] at hl
      rcases hl with rfl | rfl
      · simp only [evalL]; push_cast; nlinarith
      · simp only [evalL]; push_cast; nlinarith

/-- the strip of width 16 has no dissection by the tile `(6,5,9)` -/
theorem no_dissection {N : ℕ} (D : Erdos634.RegionDissection.CongruentRegionDissection N)
    (hR : D.region = strip 16 5 (10 * Real.sqrt 2)) (hM : HasSides D.model 6 5 9) : False := by
  obtain ⟨k1, k2, k3⟩ := Refl.MSTR23w16.MODEL_sides
  exact Refl.MSTR23w16.not_region_dissection D (by rw [hR, region_eq]) (congruent_of_hasSides' (hasSides_rot hM) k1 k2 k3)

end WSTR23w16

/-! ## `STR23w22`: width 22, tile (6,5,9) -/

namespace WSTR23w22

theorem hD : (0 : ℝ) < 2 := by norm_num
theorem e0 (X Y : ℝ) : evalL (Refl.MSTR23w22.inst.tgt.edge 0) X Y = 88 * Y := by
  first
    | (simp [Refl.MSTR23w22.inst, _root_.Tri.edge, _root_.Tri.vert, linOf, evalL, pt]; done)
    | (simp [Refl.MSTR23w22.inst, _root_.Tri.edge, _root_.Tri.vert, linOf, evalL, pt]; ring)
theorem e1 (X Y : ℝ) : evalL (Refl.MSTR23w22.inst.tgt.edge 1) X Y = -40 * X - 68 * Y + 3520 := by
  first
    | (simp [Refl.MSTR23w22.inst, _root_.Tri.edge, _root_.Tri.vert, linOf, evalL, pt]; done)
    | (simp [Refl.MSTR23w22.inst, _root_.Tri.edge, _root_.Tri.vert, linOf, evalL, pt]; ring)
theorem e2 (X Y : ℝ) : evalL (Refl.MSTR23w22.inst.tgt.edge 2) X Y = 40 * X - 20 * Y := by
  first
    | (simp [Refl.MSTR23w22.inst, _root_.Tri.edge, _root_.Tri.vert, linOf, evalL, pt]; done)
    | (simp [Refl.MSTR23w22.inst, _root_.Tri.edge, _root_.Tri.vert, linOf, evalL, pt]; ring)
theorem tgt_ok : Refl.MSTR23w22.inst.tgt.ok = true := by decide +kernel

theorem region_eq : Refl.MSTR23w22.inst.tgt.carr 2 ∩ extSet 2 Refl.MSTR23w22.ext = strip 22 5 (10 * Real.sqrt 2) := by
  ext p
  obtain ⟨X, Y, rfl⟩ := exists_rp hD p
  constructor
  · rintro ⟨hT, hE⟩
    have a0 := Tri.edge_nonneg 2 hD Refl.MSTR23w22.inst.tgt tgt_ok X Y hT 0 (by norm_num)
    have a2 := Tri.edge_nonneg 2 hD Refl.MSTR23w22.inst.tgt tgt_ok X Y hT 2 (by norm_num)
    rw [e0] at a0; rw [e2] at a2
    have x1 := (mem_halfL_rp 2 hD _ X Y).mp (hE ⟨-10, 5, 220⟩ (by simp [Refl.MSTR23w22.ext]))
    have x2 := (mem_halfL_rp 2 hD _ X Y).mp (hE ⟨0, -22, 220⟩ (by simp [Refl.MSTR23w22.ext]))
    simp only [evalL] at x1 x2
    push_cast at x1 x2
    refine ⟨(40 * X - 20 * Y) / 880, Y / 10, ?_, ?_, ?_, ?_, ?_⟩
    · apply div_nonneg <;> linarith
    · rw [div_le_one (by norm_num)]; linarith
    · apply div_nonneg <;> linarith
    · rw [div_le_one (by norm_num)]; linarith
    · unfold rp sr
      congr 1
      · ring
      · ring
  · rintro ⟨σ, τ, hs0, hs1, ht0, ht1, hp⟩
    have hXY : rp 2 X Y = rp 2 (22 * σ + 5 * τ) (10 * τ) := by
      rw [hp]; unfold rp sr; congr 1; ring
    rw [hXY]
    refine ⟨Tri.mem_of_edges 2 hD _ tgt_ok _ _ ?_, ?_⟩
    · intro i hi
      interval_cases i
      · rw [e0]; nlinarith
      · rw [e1]; nlinarith
      · rw [e2]; nlinarith
    · intro l hl
      refine (mem_halfL_rp 2 hD l _ _).mpr ?_
      simp only [Refl.MSTR23w22.ext, List.mem_cons, List.mem_nil_iff, or_false] at hl
      rcases hl with rfl | rfl
      · simp only [evalL]; push_cast; nlinarith
      · simp only [evalL]; push_cast; nlinarith

/-- the strip of width 22 has no dissection by the tile `(6,5,9)` -/
theorem no_dissection {N : ℕ} (D : Erdos634.RegionDissection.CongruentRegionDissection N)
    (hR : D.region = strip 22 5 (10 * Real.sqrt 2)) (hM : HasSides D.model 6 5 9) : False := by
  obtain ⟨k1, k2, k3⟩ := Refl.MSTR23w22.MODEL_sides
  exact Refl.MSTR23w22.not_region_dissection D (by rw [hR, region_eq]) (congruent_of_hasSides' (hasSides_rot hM) k1 k2 k3)

end WSTR23w22

/-! ## `STR34w21`: width 21, tile (12,7,16) -/

namespace WSTR34w21

theorem hD : (0 : ℝ) < 55 := by norm_num
theorem e0 (X Y : ℝ) : evalL (Refl.MSTR34w21.inst.tgt.edge 0) X Y = 84 * Y := by
  first
    | (simp [Refl.MSTR34w21.inst, _root_.Tri.edge, _root_.Tri.vert, linOf, evalL, pt]; done)
    | (simp [Refl.MSTR34w21.inst, _root_.Tri.edge, _root_.Tri.vert, linOf, evalL, pt]; ring)
theorem e1 (X Y : ℝ) : evalL (Refl.MSTR34w21.inst.tgt.edge 1) X Y = -14 * X - 42 * Y + 1176 := by
  first
    | (simp [Refl.MSTR34w21.inst, _root_.Tri.edge, _root_.Tri.vert, linOf, evalL, pt]; done)
    | (simp [Refl.MSTR34w21.inst, _root_.Tri.edge, _root_.Tri.vert, linOf, evalL, pt]; ring)
theorem e2 (X Y : ℝ) : evalL (Refl.MSTR34w21.inst.tgt.edge 2) X Y = 14 * X - 42 * Y := by
  first
    | (simp [Refl.MSTR34w21.inst, _root_.Tri.edge, _root_.Tri.vert, linOf, evalL, pt]; done)
    | (simp [Refl.MSTR34w21.inst, _root_.Tri.edge, _root_.Tri.vert, linOf, evalL, pt]; ring)
theorem tgt_ok : Refl.MSTR34w21.inst.tgt.ok = true := by decide +kernel

theorem region_eq : Refl.MSTR34w21.inst.tgt.carr 55 ∩ extSet 55 Refl.MSTR34w21.ext = strip 21 (21/2) ((7/2) * Real.sqrt 55) := by
  ext p
  obtain ⟨X, Y, rfl⟩ := exists_rp hD p
  constructor
  · rintro ⟨hT, hE⟩
    have a0 := Tri.edge_nonneg 55 hD Refl.MSTR34w21.inst.tgt tgt_ok X Y hT 0 (by norm_num)
    have a2 := Tri.edge_nonneg 55 hD Refl.MSTR34w21.inst.tgt tgt_ok X Y hT 2 (by norm_num)
    rw [e0] at a0; rw [e2] at a2
    have x1 := (mem_halfL_rp 55 hD _ X Y).mp (hE ⟨-7, 21, 147⟩ (by simp [Refl.MSTR34w21.ext]))
    have x2 := (mem_halfL_rp 55 hD _ X Y).mp (hE ⟨0, -84, 294⟩ (by simp [Refl.MSTR34w21.ext]))
    simp only [evalL] at x1 x2
    push_cast at x1 x2
    refine ⟨(14 * X - 42 * Y) / 294, Y / (7/2), ?_, ?_, ?_, ?_, ?_⟩
    · apply div_nonneg <;> linarith
    · rw [div_le_one (by norm_num)]; linarith
    · apply div_nonneg <;> linarith
    · rw [div_le_one (by norm_num)]; linarith
    · unfold rp sr
      congr 1
      · ring
      · ring
  · rintro ⟨σ, τ, hs0, hs1, ht0, ht1, hp⟩
    have hXY : rp 55 X Y = rp 55 (21 * σ + (21/2) * τ) ((7/2) * τ) := by
      rw [hp]; unfold rp sr; congr 1; ring
    rw [hXY]
    refine ⟨Tri.mem_of_edges 55 hD _ tgt_ok _ _ ?_, ?_⟩
    · intro i hi
      interval_cases i
      · rw [e0]; nlinarith
      · rw [e1]; nlinarith
      · rw [e2]; nlinarith
    · intro l hl
      refine (mem_halfL_rp 55 hD l _ _).mpr ?_
      simp only [Refl.MSTR34w21.ext, List.mem_cons, List.mem_nil_iff, or_false] at hl
      rcases hl with rfl | rfl
      · simp only [evalL]; push_cast; nlinarith
      · simp only [evalL]; push_cast; nlinarith

/-- the strip of width 21 has no dissection by the tile `(12,7,16)` -/
theorem no_dissection {N : ℕ} (D : Erdos634.RegionDissection.CongruentRegionDissection N)
    (hR : D.region = strip 21 (21/2) ((7/2) * Real.sqrt 55)) (hM : HasSides D.model 12 7 16) : False := by
  obtain ⟨k1, k2, k3⟩ := Refl.MSTR34w21.MODEL_sides
  exact Refl.MSTR34w21.not_region_dissection D (by rw [hR, region_eq]) (congruent_of_hasSides' (hasSides_rot hM) k1 k2 k3)

end WSTR34w21

/-- **The five searched instances of `rem:e2strip`.** -/
theorem e2strip_instances :
    (∀ s ∈ ([4, 10, 16, 22] : List ℝ), ∀ (N : ℕ) (D : Erdos634.RegionDissection.CongruentRegionDissection N),
        D.region = strip s 5 (10 * Real.sqrt 2) → HasSides D.model 6 5 9 → False) ∧
    (∀ (N : ℕ) (D : Erdos634.RegionDissection.CongruentRegionDissection N),
        D.region = strip 21 (21/2) ((7/2) * Real.sqrt 55) → HasSides D.model 12 7 16 → False) := by
  refine ⟨?_, fun N D hR hM => WSTR34w21.no_dissection D hR hM⟩
  intro s hs N D hR hM
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl
  · exact WSTR23w4.no_dissection D hR hM
  · exact WSTR23w10.no_dissection D hR hM
  · exact WSTR23w16.no_dissection D hR hM
  · exact WSTR23w22.no_dissection D hR hM

end Erdos634.Draft.E2StripInstances

#print axioms Erdos634.Draft.E2StripInstances.e2strip_instances
