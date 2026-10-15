-- No sorry, no native_decide.
-- Hand-built bare `Dissection 3` of T = (0,0),(4,0),(0,4) into P = (0,0),(2,0),(1,2), Q = (0,0),(1,2),(0,4),
-- R = (2,0),(4,0),(0,4) (NOT congruent; (1,2) is a T-junction: vertex of P, Q in the open edge of R).
-- Point-level applications of wall_cover, leftDir_antiparallel, sameside_edges_subsingleton,
-- edge_interior_or_side, eDir_of_side.
import Erdos634.Draft.TJCHelp

namespace Erdos634.Draft.TJCHand

open Erdos634.Geometry Erdos634.CertCoord Erdos634.Draft.TJCHelp Erdos634.CertGeom

noncomputable def T : Tri := mkTri 0 0 4 0 0 4 (by norm_num [det3])
noncomputable def P : Tri := mkTri 0 0 2 0 1 2 (by norm_num [det3])
noncomputable def Q : Tri := mkTri 0 0 1 2 0 4 (by norm_num [det3])
noncomputable def R : Tri := mkTri 2 0 4 0 0 4 (by norm_num [det3])

noncomputable def tile : Fin 3 → Tri := ![P, Q, R]

theorem inT (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ 4) : mkPt a b ∈ T.carrier := by
  have := mem_carrier_of_dets (x₀ := 0) (y₀ := 0) (x₁ := 4) (y₁ := 0) (x₂ := 0) (y₂ := 4) (a := a) (b := b)
    (by norm_num [det3]) (by norm_num [det3]; linarith) (by norm_num [det3]; linarith)
    (by norm_num [det3]; linarith)
  exact this

theorem hsub : ∀ i, (tile i).carrier ⊆ T.carrier := by
  intro i
  apply carrier_subset_of_pts_mem
  intro k
  fin_cases i <;> fin_cases k
  · exact inT 0 0 (by norm_num) (by norm_num) (by norm_num)
  · exact inT 2 0 (by norm_num) (by norm_num) (by norm_num)
  · exact inT 1 2 (by norm_num) (by norm_num) (by norm_num)
  · exact inT 0 0 (by norm_num) (by norm_num) (by norm_num)
  · exact inT 1 2 (by norm_num) (by norm_num) (by norm_num)
  · exact inT 0 4 (by norm_num) (by norm_num) (by norm_num)
  · exact inT 2 0 (by norm_num) (by norm_num) (by norm_num)
  · exact inT 4 0 (by norm_num) (by norm_num) (by norm_num)
  · exact inT 0 4 (by norm_num) (by norm_num) (by norm_num)

theorem sepH (A B : Tri) (px py qx qy : ℝ) (hne : px ≠ qx ∨ py ≠ qy)
    (hA : ∀ k, lineFun px py qx qy (A.pts k) ≤ 0) (hB : ∀ k, 0 ≤ lineFun px py qx qy (B.pts k)) :
    ∃ (f : Plane →ᵃ[ℝ] ℝ) (_ : f.linear ≠ 0) (c : ℝ),
      (∀ x ∈ A.carrier, f x ≤ c) ∧ (∀ x ∈ B.carrier, c ≤ f x) := by
  refine ⟨lineFun px py qx qy, lineFun_linear_ne_zero hne, 0, ?_, ?_⟩
  · exact le_of_forall_pts_le _ hA
  · intro x hx
    have := le_of_forall_pts_le (t := B) (-(lineFun px py qx qy)) (c := 0) (fun k => by
      simpa using hB k) x hx
    simpa using this

theorem hdisj : Pairwise fun i j => Disjoint (interior (tile i).carrier) (interior (tile j).carrier) :=
  pairwise_disjoint_of_separating tile (by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · -- P ≤ 0 ≤ Q for y - 2x
      refine sepH P Q 0 0 1 2 (by norm_num) ?_ ?_ <;> intro k <;> fin_cases k <;>
        simp [tile, P, Q, mkPt_zero, mkPt_one] <;> norm_num
    · refine sepH P R 0 4 2 0 (by norm_num) ?_ ?_ <;> intro k <;> fin_cases k <;>
        simp [tile, P, R, mkPt_zero, mkPt_one] <;> norm_num
    · refine sepH Q P 1 2 0 0 (by norm_num) ?_ ?_ <;> intro k <;> fin_cases k <;>
        simp [tile, P, Q, mkPt_zero, mkPt_one] <;> norm_num
    · exact absurd rfl hij
    · refine sepH Q R 0 4 2 0 (by norm_num) ?_ ?_ <;> intro k <;> fin_cases k <;>
        simp [tile, Q, R, mkPt_zero, mkPt_one] <;> norm_num
    · refine sepH R P 2 0 0 4 (by norm_num) ?_ ?_ <;> intro k <;> fin_cases k <;>
        simp [tile, P, R, mkPt_zero, mkPt_one] <;> norm_num
    · refine sepH R Q 2 0 0 4 (by norm_num) ?_ ?_ <;> intro k <;> fin_cases k <;>
        simp [tile, Q, R, mkPt_zero, mkPt_one] <;> norm_num
    · exact absurd rfl hij)

theorem hdet : ∑ i, |Erdos634.AreaDet.detTri (tile i)| = |Erdos634.AreaDet.detTri T| := by
  rw [Fin.sum_univ_three]
  show |Erdos634.AreaDet.detTri P| + |Erdos634.AreaDet.detTri Q| + |Erdos634.AreaDet.detTri R| = _
  simp only [T, P, Q, R, detTri_mkTri]
  norm_num [det3]

/-- the hand-built dissection -/
noncomputable def D : Dissection 3 := Erdos634.AreaDet.ofDetCertificate T tile hsub hdisj hdet

theorem D_target : D.target = T := rfl
theorem D_tile : D.tile = tile := rfl

end Erdos634.Draft.TJCHand
