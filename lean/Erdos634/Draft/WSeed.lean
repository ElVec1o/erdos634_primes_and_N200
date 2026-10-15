-- Draft/WSeed.lean — step (e) of the 7m² plan: transport a certified triangle tiling onto
-- `Φ''Wt m` by an isometry (SSS), and the seeds W_2 (28 tiles), W_3 (63 tiles).
import Erdos634.Draft.WAdd
import Erdos634.CevianTiling28Bridge
import Erdos634.CevianTiling63Bridge
import Erdos634.Draft.RefineTiles

open scoped Classical
open Erdos634.Geometry Erdos634.CertCoord
open Erdos634.Draft.CollarParam (s15 s15_pos s15_sq Rect RTiling.cast RTiling.castN)

namespace Erdos634.Draft.WSeed
open Erdos634.Draft.WFrame Erdos634.Draft.RegionTiling Erdos634.Draft.WBrick Erdos634.Draft.WAdd

theorem Wt_convex (m : ℝ) : Convex ℝ (Wt m) := by
  intro x hx y hy a b ha hb hab
  obtain ⟨x1, x2, x3⟩ := hx
  obtain ⟨y1, y2, y3⟩ := hy
  simp only [Wt, Set.mem_setOf_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul]
  refine ⟨?_, ?_, ?_⟩
  · nlinarith [mul_le_mul_of_nonneg_left x1 ha, mul_le_mul_of_nonneg_left y1 hb]
  · nlinarith [mul_le_mul_of_nonneg_left x2 ha, mul_le_mul_of_nonneg_left y2 hb]
  · nlinarith [mul_le_mul_of_nonneg_left x3 ha, mul_le_mul_of_nonneg_left y3 hb]

theorem hull_Wt (m : ℝ) (hm : 0 < m) :
    convexHull ℝ {((6 * m : ℝ), (0 : ℝ)), (6 * m, 7 * m), (0, 7 * m)} = Wt m := by
  apply Set.Subset.antisymm
  · refine convexHull_min ?_ (Wt_convex m)
    intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl
    · exact ⟨le_refl _, by linarith, by simp; linarith⟩
    · exact ⟨le_refl _, le_refl _, by simp; linarith⟩
    · exact ⟨by linarith, le_refl _, by simp; linarith⟩
  · intro p hp
    obtain ⟨h1, h2, h3⟩ := hp
    have hc := convex_convexHull ℝ ({((6 * m : ℝ), (0 : ℝ)), (6 * m, 7 * m), (0, 7 * m)} : Set (ℝ × ℝ))
    have := hc.sum_mem (t := (Finset.univ : Finset (Fin 3)))
      (w := ![1 - p.2 / (7 * m), p.2 / (7 * m) + p.1 / (6 * m) - 1, 1 - p.1 / (6 * m)])
      (z := ![((6 * m : ℝ), (0 : ℝ)), (6 * m, 7 * m), (0, 7 * m)])
      (by
        intro i _
        fin_cases i <;> simp
        · rw [div_le_one (by positivity)]; exact h2
        · have : 1 ≤ p.2 / (7 * m) + p.1 / (6 * m) := by
            rw [div_add_div _ _ (by positivity) (by positivity), le_div_iff₀ (by positivity)]
            nlinarith
          linarith
        · rw [div_le_one (by positivity)]; exact h1)
      (by simp [Fin.sum_univ_three] <;> ring)
      (by intro i _; fin_cases i <;> exact subset_convexHull ℝ _ (by simp))
    convert this using 1
    ext <;> simp [Fin.sum_univ_three] <;> field_simp <;> ring

/-- The triangle `(6m,0),(6m,7m),(0,7m)` in the W-frame. -/
noncomputable def Wtri (m : ℝ) (hm : 0 < m) : Tri :=
  triC (6 * m, 0) (6 * m, 7 * m) (0, 7 * m) (by
    intro h; nlinarith [mul_pos hm hm])

theorem carrier_Wtri (m : ℝ) (hm : 0 < m) : (Wtri m hm).carrier = Phi '' Wt m := by
  rw [Wtri, carrier_triC, hull_Wt m hm]

/-- Transport a `CongruentDissection` onto a congruent triangle's carrier. -/
theorem seed_of_cd {N : ℕ} (D : CongruentDissection N) (T : Tri) (M : Tri)
    (hT : D.target.Congruent T) (hM : D.model.Congruent M) : Nonempty (RTiling T.carrier M N) := by
  obtain ⟨g, σ, hg⟩ := hT
  have hcar : g '' D.target.carrier = T.carrier := by
    have h1 := Erdos634.DissectionMap.mapTri_carrier (Erdos634.Ladder.isoAff g) D.target
    simp only [Erdos634.Ladder.isoAff_coe] at h1
    rw [← h1]
    simp only [Tri.carrier]
    congr 1
    ext x
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨σ k, by simp [Erdos634.DissectionMap.mapTri, Erdos634.Ladder.isoAff_coe, hg]⟩
    · rintro ⟨j, rfl⟩
      obtain ⟨k, rfl⟩ := σ.surjective j
      exact ⟨k, by simp [Erdos634.DissectionMap.mapTri, Erdos634.Ladder.isoAff_coe, hg]⟩
  exact ⟨Erdos634.Draft.RegionTiling.remodel (RTiling.cast hcar (Erdos634.Draft.RegionTiling.map (ofCD D) g)) hM⟩

open Erdos634.CevianTiling28Bridge in
theorem seed28 : Nonempty (RTiling (Phi '' Wt 2) MW 28) := by
  have hT : (dissection).target.Congruent (Wtri 2 (by norm_num)) := by
    obtain ⟨s01, s12, s20⟩ := targetTri_sides
    refine ((Erdos634.SssCongruent.congruent_of_dist_three (T := targetTri)
      (U := (Wtri 2 (by norm_num)).relabel (Equiv.swap (0 : Fin 3) 1)) ?_ ?_ ?_).trans
      ((Wtri 2 (by norm_num)).congruent_relabel (Equiv.swap (0 : Fin 3) 1)).symm)
    · refine Erdos634.Draft.SumTwoSquares.eqsq dist_nonneg dist_nonneg ?_
      rw [s01]; simp only [Tri.relabel_pts, Wtri, triC_pts]; simp [Equiv.swap_apply_def]
      rw [sq_Phi]; norm_num
    · refine Erdos634.Draft.SumTwoSquares.eqsq dist_nonneg dist_nonneg ?_
      rw [s12]; simp only [Tri.relabel_pts, Wtri, triC_pts]; simp [Equiv.swap_apply_def]
      rw [sq_Phi]; norm_num
    · refine Erdos634.Draft.SumTwoSquares.eqsq dist_nonneg dist_nonneg ?_
      rw [s20]; simp only [Tri.relabel_pts, Wtri, triC_pts]; simp [Equiv.swap_apply_def]
      rw [sq_Phi]; norm_num
  have hM : (dissection).model.Congruent MW := by
    have e02 : CevianTiling28.dist2 (vertexOf CevianTiling28.tiles.headI 0)
        (vertexOf CevianTiling28.tiles.headI 2) = ((576 : ℤ), (0 : ℤ)) := by decide
    have e21 : CevianTiling28.dist2 (vertexOf CevianTiling28.tiles.headI 2)
        (vertexOf CevianTiling28.tiles.headI 1) = ((256 : ℤ), (0 : ℤ)) := by decide
    have e10 : CevianTiling28.dist2 (vertexOf CevianTiling28.tiles.headI 1)
        (vertexOf CevianTiling28.tiles.headI 0) = ((1024 : ℤ), (0 : ℤ)) := by decide
    have h1 : dist ((pieceTri headI_mem_tiles).pts 0) ((pieceTri headI_mem_tiles).pts 2) ^ 2 = 576 := by
      rw [pieceTri_dist_sq _ headI_mem_tiles 0 2]; rw [e02]; simp [Erdos634.Z15Real.toR]
    have h2 : dist ((pieceTri headI_mem_tiles).pts 2) ((pieceTri headI_mem_tiles).pts 1) ^ 2 = 256 := by
      rw [pieceTri_dist_sq _ headI_mem_tiles 2 1]; rw [e21]; simp [Erdos634.Z15Real.toR]
    have h3 : dist ((pieceTri headI_mem_tiles).pts 1) ((pieceTri headI_mem_tiles).pts 0) ^ 2 = 1024 := by
      rw [pieceTri_dist_sq _ headI_mem_tiles 1 0]; rw [e10]; simp [Erdos634.Z15Real.toR]
    refine ((pieceTri headI_mem_tiles).congruent_relabel (Equiv.swap (1 : Fin 3) 2)).trans ?_
    refine Erdos634.SssCongruent.congruent_of_dist_three ?_ ?_ ?_
    · refine Erdos634.Draft.SumTwoSquares.eqsq dist_nonneg dist_nonneg ?_
      simp only [Tri.relabel_pts, MW, brickL, triC_pts]
      rw [show ((Equiv.swap (1 : Fin 3) 2) 0 : Fin 3) = 0 from rfl,
        show ((Equiv.swap (1 : Fin 3) 2) 1 : Fin 3) = 2 from rfl, h1]
      change (576 : ℝ) = dist (Phi (0, 0)) (Phi (3, 0)) ^ 2
      rw [sq_Phi]; norm_num
    · refine Erdos634.Draft.SumTwoSquares.eqsq dist_nonneg dist_nonneg ?_
      simp only [Tri.relabel_pts, MW, brickL, triC_pts]
      rw [show ((Equiv.swap (1 : Fin 3) 2) 1 : Fin 3) = 2 from rfl,
        show ((Equiv.swap (1 : Fin 3) 2) 2 : Fin 3) = 1 from rfl, h2]
      change (256 : ℝ) = dist (Phi (3, 0)) (Phi (3, 2)) ^ 2
      rw [sq_Phi]; norm_num
    · refine Erdos634.Draft.SumTwoSquares.eqsq dist_nonneg dist_nonneg ?_
      simp only [Tri.relabel_pts, MW, brickL, triC_pts]
      rw [show ((Equiv.swap (1 : Fin 3) 2) 2 : Fin 3) = 1 from rfl,
        show ((Equiv.swap (1 : Fin 3) 2) 0 : Fin 3) = 0 from rfl, h3]
      change (1024 : ℝ) = dist (Phi (3, 2)) (Phi (0, 0)) ^ 2
      rw [sq_Phi]; norm_num
  obtain ⟨R⟩ := seed_of_cd dissection (Wtri 2 (by norm_num)) MW hT hM
  exact ⟨RTiling.castN tiles_length_eq_28 (RTiling.cast (carrier_Wtri 2 (by norm_num)) R)⟩

open Erdos634.CevianTiling63Bridge in
theorem seed63 : Nonempty (RTiling (Phi '' Wt 3) MW 63) := by
  have hT : (dissection).target.Congruent (Wtri 3 (by norm_num)) := by
    obtain ⟨s01, s12, s20⟩ := targetTri_sides
    refine ((Erdos634.SssCongruent.congruent_of_dist_three (T := targetTri)
      (U := (Wtri 3 (by norm_num)).relabel (Equiv.swap (0 : Fin 3) 1)) ?_ ?_ ?_).trans
      ((Wtri 3 (by norm_num)).congruent_relabel (Equiv.swap (0 : Fin 3) 1)).symm)
    · refine Erdos634.Draft.SumTwoSquares.eqsq dist_nonneg dist_nonneg ?_
      rw [s01]; simp only [Tri.relabel_pts, Wtri, triC_pts]; simp [Equiv.swap_apply_def]
      rw [sq_Phi]; norm_num
    · refine Erdos634.Draft.SumTwoSquares.eqsq dist_nonneg dist_nonneg ?_
      rw [s12]; simp only [Tri.relabel_pts, Wtri, triC_pts]; simp [Equiv.swap_apply_def]
      rw [sq_Phi]; norm_num
    · refine Erdos634.Draft.SumTwoSquares.eqsq dist_nonneg dist_nonneg ?_
      rw [s20]; simp only [Tri.relabel_pts, Wtri, triC_pts]; simp [Equiv.swap_apply_def]
      rw [sq_Phi]; norm_num
  have hM : (dissection).model.Congruent MW := by
    have e01 : CevianTiling63.dist2 (vertexOf CevianTiling63.tiles.headI 0)
        (vertexOf CevianTiling63.tiles.headI 1) = ((576 : ℤ), (0 : ℤ)) := by decide
    have e12 : CevianTiling63.dist2 (vertexOf CevianTiling63.tiles.headI 1)
        (vertexOf CevianTiling63.tiles.headI 2) = ((256 : ℤ), (0 : ℤ)) := by decide
    have e20 : CevianTiling63.dist2 (vertexOf CevianTiling63.tiles.headI 2)
        (vertexOf CevianTiling63.tiles.headI 0) = ((1024 : ℤ), (0 : ℤ)) := by decide
    have h1 : dist ((pieceTri headI_mem_tiles).pts 0) ((pieceTri headI_mem_tiles).pts 1) ^ 2 = 576 := by
      rw [pieceTri_dist_sq _ headI_mem_tiles 0 1]; rw [e01]; simp [Erdos634.Z15Real.toR]
    have h2 : dist ((pieceTri headI_mem_tiles).pts 1) ((pieceTri headI_mem_tiles).pts 2) ^ 2 = 256 := by
      rw [pieceTri_dist_sq _ headI_mem_tiles 1 2]; rw [e12]; simp [Erdos634.Z15Real.toR]
    have h3 : dist ((pieceTri headI_mem_tiles).pts 2) ((pieceTri headI_mem_tiles).pts 0) ^ 2 = 1024 := by
      rw [pieceTri_dist_sq _ headI_mem_tiles 2 0]; rw [e20]; simp [Erdos634.Z15Real.toR]
    refine Erdos634.SssCongruent.congruent_of_dist_three ?_ ?_ ?_
    · refine Erdos634.Draft.SumTwoSquares.eqsq dist_nonneg dist_nonneg ?_
      show dist ((pieceTri headI_mem_tiles).pts 0) ((pieceTri headI_mem_tiles).pts 1) ^ 2 = _
      simp only [MW, brickL, triC_pts]
      rw [h1]
      change (576 : ℝ) = dist (Phi (0, 0)) (Phi (3, 0)) ^ 2
      rw [sq_Phi]; norm_num
    · refine Erdos634.Draft.SumTwoSquares.eqsq dist_nonneg dist_nonneg ?_
      show dist ((pieceTri headI_mem_tiles).pts 1) ((pieceTri headI_mem_tiles).pts 2) ^ 2 = _
      simp only [MW, brickL, triC_pts]
      rw [h2]
      change (256 : ℝ) = dist (Phi (3, 0)) (Phi (3, 2)) ^ 2
      rw [sq_Phi]; norm_num
    · refine Erdos634.Draft.SumTwoSquares.eqsq dist_nonneg dist_nonneg ?_
      show dist ((pieceTri headI_mem_tiles).pts 2) ((pieceTri headI_mem_tiles).pts 0) ^ 2 = _
      simp only [MW, brickL, triC_pts]
      rw [h3]
      change (1024 : ℝ) = dist (Phi (3, 2)) (Phi (0, 0)) ^ 2
      rw [sq_Phi]; norm_num
  obtain ⟨R⟩ := seed_of_cd dissection (Wtri 3 (by norm_num)) MW hT hM
  exact ⟨RTiling.castN tiles_length_eq_63 (RTiling.cast (carrier_Wtri 3 (by norm_num)) R)⟩

end Erdos634.Draft.WSeed

#print axioms Erdos634.Draft.WSeed.seed28
#print axioms Erdos634.Draft.WSeed.seed63
