import Mathlib.Tactic
import Erdos634.Draft.ThmDWall
import Erdos634.MarchInduction

/-!
Credit: the method (rigidity window, Lemmas 30-34, row induction, Theorem 37) is adapted from M. Beeson and G. Rosu, 'Tiling a triangle into a prime number of congruent triangles' (preprint, 16 Oct 2026); the transfer to the tile with gamma = 2 alpha (fan lemma at straight points, windows u and v, Lemma K) is ours.
# Theorem D' item (4): a point in the relative interior of a tile edge has the tile on its half-disc  

`westCover_of_edge` : `P` in the relative interior of the edge `[A, B]` of a tile `T` lying in `{Φ ≤ Φ P}` with the third vertex strictly
below: every point `y` close to `P` with `Φ y < Φ P` is interior to `T` (`WestCover`).
-/

open scoped Classical
open Metric
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Erdos634.Draft.ThmDRun

open Erdos634.Geometry Set Erdos634.Draft.ThmDHalf

variable {N : ℕ}

theorem Tri.coord_pos_mem_interior (T : Tri) {y : Plane} (h : ∀ i, 0 < T.basis.coord i y) :
    y ∈ interior T.carrier := by
  have hopen : IsOpen {z : Plane | ∀ i, 0 < T.basis.coord i z} := by
    simp only [Set.setOf_forall]
    refine isOpen_iInter_of_finite fun i => isOpen_lt continuous_const ?_
    exact (T.basis.coord i).continuous_of_finiteDimensional
  refine interior_maximal ?_ hopen h
  intro z hz
  rw [T.carrier_eq_nonneg_coord]
  exact fun i => (hz i).le

theorem westCover_of_edge {D : Dissection N} (Φ : Plane →ₗ[ℝ] ℝ) {P : Plane} (t : Fin N) {k m j : Fin 3}
    (hkm : k ≠ m) (hkj : k ≠ j) (hmj : m ≠ j)
    (hP : P ∈ openSegment ℝ ((D.tile t).pts k) ((D.tile t).pts m))
    (hk : Φ ((D.tile t).pts k) = Φ P) (hm : Φ ((D.tile t).pts m) = Φ P)
    (hle : ∀ i, Φ ((D.tile t).pts i) ≤ Φ P) (hj : Φ ((D.tile t).pts j) < Φ P) :
    WestCover D Φ P := by
  set T := D.tile t with hT
  set c0 := Φ P with hc0
  rw [openSegment_eq_image_lineMap] at hP
  obtain ⟨s, ⟨hs0, hs1⟩, hPs⟩ := hP
  -- barycentric coordinates at `P`
  have hck : T.basis.coord k P = 1 - s := by
    rw [← hPs, AffineMap.apply_lineMap]
    have e1 : T.basis.coord k (T.pts k) = 1 := AffineBasis.coord_apply_eq T.basis k
    have e2 : T.basis.coord k (T.pts m) = 0 := AffineBasis.coord_apply_ne T.basis hkm
    rw [e1, e2, AffineMap.lineMap_apply]; simp; ring
  have hcm : T.basis.coord m P = s := by
    rw [← hPs, AffineMap.apply_lineMap]
    have e1 : T.basis.coord m (T.pts k) = 0 := AffineBasis.coord_apply_ne T.basis hkm.symm
    have e2 : T.basis.coord m (T.pts m) = 1 := AffineBasis.coord_apply_eq T.basis m
    rw [e1, e2, AffineMap.lineMap_apply]; simp
  -- continuity: near `P` the coordinates of `k` and `m` stay positive
  have hevk : ∀ᶠ y in nhds P, 0 < T.basis.coord k y :=
    ((T.basis.coord k).continuous_of_finiteDimensional.continuousAt).eventually (lt_mem_nhds (by rw [hck]; linarith))
  have hevm : ∀ᶠ y in nhds P, 0 < T.basis.coord m y :=
    ((T.basis.coord m).continuous_of_finiteDimensional.continuousAt).eventually (lt_mem_nhds (by rw [hcm]; linarith))
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp (hevk.and hevm)
  refine ⟨t, δ, hδ, fun y hyd hyΦ => ?_, fun y hy => ?_⟩
  · obtain ⟨hyk, hym⟩ := hball hyd
    apply Tri.coord_pos_mem_interior
    intro i
    -- the third coordinate
    have hsum : ∑ i, T.basis.coord i y = 1 := T.basis.sum_coord_apply_eq_one y
    have hlin : ∑ i, T.basis.coord i y • T.pts i = y := T.basis.linear_combination_coord_eq_self y
    have hΦy : Φ y = ∑ i, T.basis.coord i y * Φ (T.pts i) := by
      conv_lhs => rw [← hlin]
      rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, smul_eq_mul]
    have hΦi : ∀ i, T.basis.coord i y * Φ (T.pts i) =
        T.basis.coord i y * c0 + (if i = j then T.basis.coord i y * (Φ (T.pts j) - c0) else 0) := by
      intro i
      rcases Erdos634.MarchInduction.fin3_cover k m j hkm hkj hmj i with rfl | rfl | rfl
      · simp [hkj, hk]
      · simp [hmj, hm]
      · simp; ring
    have hcj : T.basis.coord j y * (Φ (T.pts j) - c0) = Φ y - c0 := by
      have h1 := hΦy
      rw [Finset.sum_congr rfl (fun i _ => hΦi i), Finset.sum_add_distrib, ← Finset.sum_mul, hsum] at h1
      simp at h1
      linarith
    have hjpos : 0 < T.basis.coord j y := by
      by_contra hneg
      push_neg at hneg
      have : T.basis.coord j y * (Φ (T.pts j) - c0) ≥ 0 := mul_nonneg_of_nonpos_of_nonpos hneg (by linarith)
      linarith
    rcases Erdos634.MarchInduction.fin3_cover k m j hkm hkj hmj i with rfl | rfl | rfl
    · exact hyk
    · exact hym
    · exact hjpos
  · have hsub : T.carrier ⊆ {z | Φ z ≤ c0} := by
      refine carrier_subset_of_pts (convex_halfSpace_le Φ.isLinear c0) T (fun i => hle i)
    exact hsub hy

#print axioms westCover_of_edge
end Erdos634.Draft.ThmDRun
