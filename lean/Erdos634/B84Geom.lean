import Erdos634.Draft.CVCCevianCut

/-!
# B84 geometry: the base-alpha target (24,24,42) as a `CongruentDissection 84` of the tile (2,3,4)  Atom `A_4@(1,2)` (apex `W`, base `U V`, legs 24, base 12) is the
existing exact tiling `FDCCevianAtom.atomTiles_four` (48 tiles).  Put `A = W + (7/4)(U-W)`.
Then `Δ = (A, W, V)` has sides `|AW| = 42`, `|WV| = 24`, `|VA| = 24` (isosceles, base 42, legs 24)
and the cevian `V U` cuts it into the atom `W U V` and the triangle `A V U` with sides
`(12, 18, 24) = 6 (2,3,4)` (36 tiles, `tileK`).  Count `36 + 48 = 84`.
-/

namespace Erdos634.B84
open Erdos634.Geometry
open Erdos634.Draft.CVCCevianCut
open Erdos634.Draft.FDBBaseBetaE1 (HasSides)
open Erdos634.Draft.FDCCevianAtom (atomTiles_four hasSides_congr)

theorem assemble84 (DA : CongruentDissection (3 * 4 ^ 2)) (ht : HasSides DA.model 2 3 4)
    (W U V : Plane) (hcar : DA.target.carrier = convexHull ℝ {W, U, V})
    (hUV : dist U V = 12) (hVW : dist V W = 24) (hWU : dist W U = 24) (hD : cr W U V ≠ 0) :
    ∃ D : CongruentDissection (6 * 6 * 1 + 3 * 4 ^ 2), HasSides D.model 2 3 4 ∧
      dist (D.target.pts 1) (D.target.pts 2) = 24 ∧ dist (D.target.pts 2) (D.target.pts 0) = 24 ∧
      dist (D.target.pts 0) (D.target.pts 1) = 42 := by
  have hUV' := sqd_of_dist _ _ _ hUV
  have hVW' := sqd_of_dist _ _ _ hVW
  have hWU' := sqd_of_dist _ _ _ hWU
  obtain ⟨A, hA⟩ : ∃ A : Plane, A = W + (7 / 4 : ℝ) • (U - W) := ⟨_, rfl⟩
  have hA0 : A 0 = W 0 + 7 / 4 * (U 0 - W 0) := by rw [hA]; simp
  have hA1 : A 1 = W 1 + 7 / 4 * (U 1 - W 1) := by rw [hA]; simp
  have c1 : cr V W A ≠ 0 := by
    have : cr V W A = 7 / 4 * cr W U V := by unfold cr; rw [hA0, hA1]; ring
    rw [this]; exact mul_ne_zero (by norm_num) hD
  have c2 : cr A V U ≠ 0 := by
    have : cr A V U = 3 / 4 * cr W U V := by unfold cr; rw [hA0, hA1]; ring
    rw [this]; exact mul_ne_zero (by norm_num) hD
  have c3 : cr A W V ≠ 0 := by
    have : cr A W V = -(7 / 4) * cr W U V := by unfold cr; rw [hA0, hA1]; ring
    rw [this]; exact mul_ne_zero (by norm_num) hD
  have dVA : dist V A = 24 := dist_of_sqd _ _ _ (by norm_num) (by
    rw [hA0, hA1]; linear_combination (21 / 16) * hWU' + (-3 / 4) * hVW' + (7 / 4) * hUV')
  have dUA : dist U A = 18 := dist_of_sqd _ _ _ (by norm_num) (by
    rw [hA0, hA1]; linear_combination (9 / 16) * hWU')
  have dAW : dist A W = 42 := dist_of_sqd _ _ _ (by norm_num) (by
    rw [hA0, hA1]; linear_combination (49 / 16) * hWU')
  let Δ : Tri := triOf A W V c3
  let T1 : Tri := triOf A V U c2
  have hs1 : HasSides T1 (((6 : ℕ) : ℝ) * 2) (((6 : ℕ) : ℝ) * 3) (((6 : ℕ) : ℝ) * 4) :=
    ⟨Equiv.refl _, by
        show dist V U = _
        rw [dist_comm, hUV]; norm_num,
      by
        show dist U A = _
        rw [dUA]; norm_num,
      by
        show dist A V = _
        rw [dist_comm, dVA]; norm_num⟩
  obtain ⟨E1, hE1c, hE1m⟩ := tileK DA.model T1 6 (by norm_num) ht hs1
  have hP : U = W + (4 / 7 : ℝ) • (A - W) := by rw [hA]; module
  have cov := fan_cover V W A U (4 / 7) (by norm_num) (by norm_num) hP
  have dis := fan_disjoint V W A U (4 / 7) (by norm_num) (by norm_num) hP c1
  have s1 : ({W, U, V} : Set Plane) = {V, W, U} := by
    ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  have s2 : ({A, V, U} : Set Plane) = {V, U, A} := by
    ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  have s3 : ({A, W, V} : Set Plane) = {V, W, A} := by
    ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  have hT1c : T1.carrier = convexHull ℝ {A, V, U} := carrier_triOf _ _ _ c2
  have hΔc : Δ.carrier = convexHull ℝ {A, W, V} := carrier_triOf _ _ _ c3
  have hcov : E1.target.carrier ∪ DA.target.carrier = Δ.carrier := by
    rw [hE1c, hT1c, hcar, hΔc, s1, s2, s3, Set.union_comm]; exact cov.symm
  have hdisj : Disjoint (interior E1.target.carrier) (interior DA.target.carrier) := by
    rw [hE1c, hT1c, hcar, s1, s2]; exact dis.symm
  let D := unionCongruentDissection Δ E1 DA hE1m hcov hdisj
  refine ⟨D, ?_, ?_, ?_, ?_⟩
  · show HasSides E1.model 2 3 4
    rw [hE1m]; exact ht
  · show dist W V = 24
    rw [dist_comm]; exact hVW
  · show dist V A = 24
    exact dVA
  · show dist A W = 42
    exact dAW

/-- **The real witness**: a `CongruentDissection 84` of the isosceles triangle with legs 24, base 42,
whose model is a tile with sides `2, 3, 4`; target vertex order `(A, W, V)` (base `A W`, apex `V`). -/
theorem b84_exists : ∃ D : CongruentDissection 84, HasSides D.model 2 3 4 ∧
      dist (D.target.pts 1) (D.target.pts 2) = 24 ∧ dist (D.target.pts 2) (D.target.pts 0) = 24 ∧
      dist (D.target.pts 0) (D.target.pts 1) = 42 := by
  obtain ⟨DA, hAs, hAm⟩ := atomTiles_four
  obtain ⟨τ, h12, h20, h01⟩ := hAs
  have h12' : dist (DA.target.pts (τ 1)) (DA.target.pts (τ 2)) = 12 := by rw [h12]; norm_num
  have h20' : dist (DA.target.pts (τ 2)) (DA.target.pts (τ 0)) = 24 := by rw [h20]; norm_num
  have h01' : dist (DA.target.pts (τ 0)) (DA.target.pts (τ 1)) = 24 := by rw [h01]; norm_num
  obtain ⟨D, hm, h1, h2, h3⟩ := assemble84 DA hAm (DA.target.pts (τ 0)) (DA.target.pts (τ 1))
    (DA.target.pts (τ 2)) (by unfold Tri.carrier; rw [range_perm DA.target τ]) h12' h20' h01'
    (cr_pts_ne_zero (DA.target.relabel τ))
  obtain ⟨E, hEt, hEm⟩ := exists_reindex (M := 84) (by norm_num) D
  exact ⟨E, by rw [hEm]; exact hm, by rw [hEt]; exact h1, by rw [hEt]; exact h2,
    by rw [hEt]; exact h3⟩

end Erdos634.B84

#print axioms Erdos634.B84.assemble84
#print axioms Erdos634.B84.b84_exists
