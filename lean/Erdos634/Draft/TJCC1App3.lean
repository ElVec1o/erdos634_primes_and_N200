-- No sorry, no native_decide.
-- C1 continued: `edge_interior_or_side` (interior case at the T-junction point X; side case at the midpoint (1,0) of tile 0's
-- base edge), `eDir_of_side` (tile 0 base edge on target side 0; tile 4 slanted edge on target side 2), and failure of the conclusions at excluded points.
import Erdos634.Draft.TJCC1App2

namespace Erdos634.Draft.TJCC1App3

open Erdos634.Geometry Erdos634.CertCoord Erdos634.Draft.TJCHelp Erdos634.Draft.G3CCert
  Erdos634.Draft.G3RCCommon Erdos634.Draft.G3RC1Tiling Erdos634.Draft.TJCC1 Erdos634.Draft.TJCC1App
  Erdos634.Draft.TJCC1App2

theorem tgt_lin (a b : ℝ) (k : Fin 3) :
    lin a b (D.target.pts k) = a * ((vtx cert.target k).1 : ℝ) + b * (((vtx cert.target k).2 : ℝ) * Real.sqrt 3) := by
  rw [tgt_pts, lin_toPt]

theorem tgt_edge0 (a b c : ℝ) (h0 : lin a b (toPt (0, 0)) = c) (h1 : lin a b (toPt (8, 0)) = c) :
    ∀ y ∈ D.target.edge 0, lin a b y = c := by
  intro y hy; unfold Tri.edge at hy
  have e0 : D.target.pts 0 = toPt (0, 0) := by rw [tgt_pts]; rfl
  have e1 : D.target.pts (0 + 1) = toPt (8, 0) := by rw [tgt_pts]; rfl
  rw [e0, e1] at hy; exact seg_eq h0 h1 hy

theorem tgt_edge1 (a b c : ℝ) (h0 : lin a b (toPt (8, 0)) = c) (h1 : lin a b (toPt (4, 4)) = c) :
    ∀ y ∈ D.target.edge 1, lin a b y = c := by
  intro y hy; unfold Tri.edge at hy
  have e0 : D.target.pts 1 = toPt (8, 0) := by rw [tgt_pts]; rfl
  have e1 : D.target.pts (1 + 1) = toPt (4, 4) := by rw [tgt_pts]; rfl
  rw [e0, e1] at hy; exact seg_eq h0 h1 hy

theorem tgt_edge2 (a b c : ℝ) (h0 : lin a b (toPt (4, 4)) = c) (h1 : lin a b (toPt (0, 0)) = c) :
    ∀ y ∈ D.target.edge 2, lin a b y = c := by
  intro y hy; unfold Tri.edge at hy
  have e0 : D.target.pts 2 = toPt (4, 4) := by rw [tgt_pts]; rfl
  have e1 : D.target.pts (2 + 1) = toPt (0, 0) := by rw [tgt_pts]; rfl
  rw [e0, e1] at hy; exact seg_eq h0 h1 hy

/-! ## (4a) `edge_interior_or_side`, interior case, at the T-junction point X on tile 2's edge 1 -/

theorem c1_eios_interior : X ∈ interior D.target.carrier := by
  have a2 : (D.tile (tl 2)).pts 1 = toPt (4, 0) := pt_toPt _ _ _ (by decide +kernel)
  have b2 : (D.tile (tl 2)).pts (1 + 1) = toPt (5, 1) := pt_toPt _ _ _ (by decide +kernel)
  have hx : X ∈ D.eSet (tl 2, 1) := X_in_tile2_edge1
  rcases D.edge_interior_or_side (tl 2, 1) hx (X_ne_pts _ _) (X_ne_pts _ _) with h | ⟨j, hj⟩
  · exact h
  · exfalso
    have hp : toPt (5, 1) ∈ D.target.edge j :=
      hj (mem_edge_of _ 1 a2 b2 (right_mem_segment ℝ _ _))
    fin_cases j
    · have := tgt_edge0 0 1 0 (by rw [lin_toPt]; push_cast; ring) (by rw [lin_toPt]; push_cast; ring) _ hp
      rw [lin_toPt] at this; push_cast at this
      nlinarith [s3pos]
    · have := tgt_edge1 (Real.sqrt 3) 1 (8 * Real.sqrt 3) (by rw [lin_toPt]; push_cast; ring)
        (by rw [lin_toPt]; push_cast; ring) _ hp
      rw [lin_toPt] at this; push_cast at this
      nlinarith [s3pos]
    · have := tgt_edge2 (Real.sqrt 3) (-1) 0 (by rw [lin_toPt]; push_cast; ring)
        (by rw [lin_toPt]; push_cast; ring) _ hp
      rw [lin_toPt] at this; push_cast at this
      nlinarith [s3pos]

/-! ## (4b) `edge_interior_or_side`, side case, at the midpoint (1,0) of tile 0's base edge -/

theorem c1_eios_side :
    ∃ j : Fin 3, D.eSet (tl 0, 0) ⊆ D.target.edge j ∧ j = 0 := by
  have a0 : (D.tile (tl 0)).pts 0 = toPt (0, 0) := pt_toPt _ _ _ (by decide +kernel)
  have b0 : (D.tile (tl 0)).pts (0 + 1) = toPt (2, 0) := pt_toPt _ _ _ (by decide +kernel)
  have hY : toPt (1, 0) ∈ D.eSet (tl 0, 0) :=
    mem_edge_of _ 0 a0 b0 (mem_seg_toPt (0, 0) (2, 0) (1, 0) (1/2) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num))
  have n1 : toPt (1, 0) ≠ (D.tile (tl 0, 0).1).pts (tl 0, 0).2 := by
    show toPt (1, 0) ≠ (D.tile (tl 0)).pts 0
    rw [a0]; intro h; exact absurd (toPt_inj h) (by decide)
  have n2 : toPt (1, 0) ≠ (D.tile (tl 0, 0).1).pts ((tl 0, 0).2 + 1) := by
    show toPt (1, 0) ≠ (D.tile (tl 0)).pts (0 + 1)
    rw [b0]; intro h; exact absurd (toPt_inj h) (by decide)
  rcases D.edge_interior_or_side (tl 0, 0) hY n1 n2 with h | ⟨j, hj⟩
  · exfalso
    have hge : ∀ y ∈ D.target.carrier, 0 ≤ lin 0 1 y := by
      refine carrier_ge D.target ?_
      intro k
      rw [tgt_lin]
      have : ((vtx cert.target k).2 : ℝ) ≥ 0 := by
        fin_cases k <;> simp [vtx, cert]
      nlinarith [s3pos]
    exact not_interior_on_line_ge (lin_ne_zero (Or.inr one_ne_zero)) (c := 0) (A := D.target.carrier) hge h
      (by rw [lin_toPt]; push_cast; ring)
  · refine ⟨j, hj, ?_⟩
    have p0 : toPt (0, 0) ∈ D.target.edge j := hj (mem_edge_of _ 0 a0 b0 (left_mem_segment ℝ _ _))
    have p2 : toPt (2, 0) ∈ D.target.edge j := hj (mem_edge_of _ 0 a0 b0 (right_mem_segment ℝ _ _))
    fin_cases j
    · rfl
    · exfalso
      have := tgt_edge1 (Real.sqrt 3) 1 (8 * Real.sqrt 3) (by rw [lin_toPt]; push_cast; ring)
        (by rw [lin_toPt]; push_cast; ring) _ p0
      rw [lin_toPt] at this; push_cast at this
      nlinarith [s3pos]
    · exfalso
      have := tgt_edge2 (Real.sqrt 3) (-1) 0 (by rw [lin_toPt]; push_cast; ring)
        (by rw [lin_toPt]; push_cast; ring) _ p2
      rw [lin_toPt] at this; push_cast at this
      nlinarith [s3pos]

/-! ## (5) `eDir_of_side` -/

theorem norm_mkPt (a b : ℝ) : ‖mkPt a b‖ = Real.sqrt (a ^ 2 + b ^ 2) := by
  rw [EuclideanSpace.norm_eq]; simp [Fin.sum_univ_two, sq_abs]

theorem tgt_ld (k : Fin 3) (p q : LP) (hp : vtx cert.target k = p) (hq : vtx cert.target (k + 1) = q) :
    D.target.leftDir k = mkPt ((q.1 : ℝ) - p.1) (((q.2 : ℝ) - p.2) * Real.sqrt 3) := by
  show (cd cert cert_ok).target.leftDir k = _
  rw [cd_target, leftDir_triOf, hp, hq, toPt_eq, toPt_eq, mkPt_sub]
  congr 1; ring

theorem unit_val (v : Plane) (n : ℝ) (hn : ‖v‖ = n) (a b : ℝ) (hv : v = mkPt a b) :
    ‖v‖⁻¹ • v = mkPt (n⁻¹ * a) (n⁻¹ * b) := by
  rw [hn, hv, mkPt_smul]

theorem c1_eDir_base :
    D.eDir (tl 0, 0) = D.target.leftUnit 0 ∧ (D.eDir (tl 0, 0)).1 = mkPt 1 0 ∧
      (D.target.leftUnit 0).1 = mkPt 1 0 := by
  have a0 : (D.tile (tl 0)).pts 0 = toPt (0, 0) := pt_toPt _ _ _ (by decide +kernel)
  have b0 : (D.tile (tl 0)).pts (0 + 1) = toPt (2, 0) := pt_toPt _ _ _ (by decide +kernel)
  have hh : D.eSet (tl 0, 0) ⊆ D.target.edge 0 := by
    intro y hy
    have hy' : y ∈ (D.tile (tl 0)).edge 0 := hy
    unfold Tri.edge at hy'; rw [a0, b0] at hy'
    have e0 : D.target.pts 0 = toPt (0, 0) := by rw [tgt_pts]; rfl
    have e1 : D.target.pts (0 + 1) = toPt (8, 0) := by rw [tgt_pts]; rfl
    show y ∈ segment ℝ (D.target.pts 0) (D.target.pts (0 + 1))
    rw [e0, e1]
    exact (convex_segment (𝕜 := ℝ) (toPt (0, 0)) (toPt (8, 0))).segment_subset (left_mem_segment ℝ _ _)
      (mem_seg_toPt (0, 0) (8, 0) (2, 0) (1/4) (by norm_num) (by norm_num) (by norm_num) (by norm_num)) hy'
  have hl : (D.tile (tl 0)).leftDir 0 = mkPt 2 0 := by
    rw [ld_val _ _ (0, 0) (2, 0) (by decide +kernel) (by decide +kernel)]
    congr 1 <;> push_cast <;> ring
  have hlT : D.target.leftDir 0 = mkPt 8 0 := by
    rw [tgt_ld _ (0, 0) (8, 0) rfl rfl]
    congr 1 <;> push_cast <;> ring
  have h1 : (D.eDir (tl 0, 0)).1 = mkPt 1 0 := by
    show ‖(D.tile (tl 0)).leftDir 0‖⁻¹ • (D.tile (tl 0)).leftDir 0 = _
    rw [hl, norm_mkPt, mkPt_smul]
    have : Real.sqrt ((2 : ℝ) ^ 2 + 0 ^ 2) = 2 := by
      rw [show ((2 : ℝ) ^ 2 + 0 ^ 2) = 2 ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)
    rw [this]; norm_num
  have h2 : (D.target.leftUnit 0).1 = mkPt 1 0 := by
    show ‖D.target.leftDir 0‖⁻¹ • D.target.leftDir 0 = _
    rw [hlT, norm_mkPt, mkPt_smul]
    have : Real.sqrt ((8 : ℝ) ^ 2 + 0 ^ 2) = 8 := by
      rw [show ((8 : ℝ) ^ 2 + 0 ^ 2) = 8 ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)
    rw [this]; norm_num
  exact ⟨D.eDir_of_side hh, h1, h2⟩

/-- tile 4's edge 0 = (4,4)->(2,2) lies on the SLANTED target side 2 = (4,4)->(0,0); both directions are `(-1/2, -√3/2)` -/
theorem c1_eDir_slant :
    D.eDir (tl 4, 0) = D.target.leftUnit 2 ∧ (D.eDir (tl 4, 0)).1 = mkPt (-1/2) (-(Real.sqrt 3) / 2) := by
  have a4 : (D.tile (tl 4)).pts 0 = toPt (4, 4) := pt_toPt _ _ _ (by decide +kernel)
  have b4 : (D.tile (tl 4)).pts (0 + 1) = toPt (2, 2) := pt_toPt _ _ _ (by decide +kernel)
  have hh : D.eSet (tl 4, 0) ⊆ D.target.edge 2 := by
    intro y hy
    have hy' : y ∈ (D.tile (tl 4)).edge 0 := hy
    unfold Tri.edge at hy'; rw [a4, b4] at hy'
    have e0 : D.target.pts 2 = toPt (4, 4) := by rw [tgt_pts]; rfl
    have e1 : D.target.pts (2 + 1) = toPt (0, 0) := by rw [tgt_pts]; rfl
    show y ∈ segment ℝ (D.target.pts 2) (D.target.pts (2 + 1))
    rw [e0, e1]
    exact (convex_segment (𝕜 := ℝ) (toPt (4, 4)) (toPt (0, 0))).segment_subset (left_mem_segment ℝ _ _)
      (mem_seg_toPt (4, 4) (0, 0) (2, 2) (1/2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)) hy'
  have hl : (D.tile (tl 4)).leftDir 0 = mkPt (-2) (-2 * Real.sqrt 3) := by
    rw [ld_val _ _ (4, 4) (2, 2) (by decide +kernel) (by decide +kernel)]
    congr 1 <;> push_cast <;> ring
  have h1 : (D.eDir (tl 4, 0)).1 = mkPt (-1/2) (-(Real.sqrt 3) / 2) := by
    show ‖(D.tile (tl 4)).leftDir 0‖⁻¹ • (D.tile (tl 4)).leftDir 0 = _
    rw [hl, norm_mkPt, mkPt_smul]
    have : Real.sqrt ((-2 : ℝ) ^ 2 + (-2 * Real.sqrt 3) ^ 2) = 4 := by
      rw [show ((-2 : ℝ) ^ 2 + (-2 * Real.sqrt 3) ^ 2) = 4 ^ 2 by nlinarith [s3sq]]
      exact Real.sqrt_sq (by norm_num)
    rw [this]; congr 1 <;> ring
  exact ⟨D.eDir_of_side hh, h1⟩

/-! ## negative controls and the T-junction in `OnEdge` form -/

theorem c1_vertex_in_vertexSet : toPt (5, 1) ∈ D.vertexSet := by
  have a2 : (D.tile (tl 2)).pts 2 = toPt (5, 1) := pt_toPt _ _ _ (by decide +kernel)
  exact Set.mem_iUnion.mpr ⟨tl 2, Set.mem_iUnion.mpr ⟨2, by simp [a2]⟩⟩

theorem c1_wall_cover_hyp_fails : ¬ (toPt (5, 1) ∉ D.vertexSet) := fun h => h c1_vertex_in_vertexSet

theorem c1_antiparallel_hyp_fails_tile2 : ¬ OnEdge D (toPt (5, 1)) (tl 2) := by
  have a2 : (D.tile (tl 2)).pts 2 = toPt (5, 1) := pt_toPt _ _ _ (by decide +kernel)
  have := vertex_not_onEdge D (tl 2) 2
  rwa [a2] at this

theorem c1_antiparallel_hyp_fails_tile3 : ¬ OnEdge D (toPt (5, 1)) (tl 3) := by
  have a3 : (D.tile (tl 3)).pts 1 = toPt (5, 1) := pt_toPt _ _ _ (by decide +kernel)
  have := vertex_not_onEdge D (tl 3) 1
  rwa [a3] at this

/-- the T-junction itself, as `OnEdge` data: (5,1) is in the relative interior of tile 6's edge 2 = (6,2)-(4,0) -/
theorem c1_T_junction_tile6 : OnEdge D (toPt (5, 1)) (tl 6) := by
  have a6 : (D.tile (tl 6)).pts 2 = toPt (6, 2) := pt_toPt _ _ _ (by decide +kernel)
  have b6 : (D.tile (tl 6)).pts (2 + 1) = toPt (4, 0) := pt_toPt _ _ _ (by decide +kernel)
  have hx : toPt (5, 1) ∈ (D.tile (tl 6)).edge 2 :=
    mem_edge_of _ 2 a6 b6 (mem_seg_toPt (6, 2) (4, 0) (5, 1) (1/2) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num))
  have h1 : toPt (5, 1) ≠ (D.tile (tl 6)).pts 2 := by
    rw [a6]; intro h; exact absurd (toPt_inj h) (by decide)
  have h2 : toPt (5, 1) ≠ (D.tile (tl 6)).pts (2 + 1) := by
    rw [b6]; intro h; exact absurd (toPt_inj h) (by decide)
  obtain ⟨hz, hp⟩ := (D.tile (tl 6)).onEdge_param hx h1 h2
  exact ⟨2 + 2, hz, hp⟩

end Erdos634.Draft.TJCC1App3

#print axioms Erdos634.Draft.TJCC1App3.c1_eios_interior
#print axioms Erdos634.Draft.TJCC1App3.c1_eios_side
#print axioms Erdos634.Draft.TJCC1App3.c1_eDir_base
#print axioms Erdos634.Draft.TJCC1App3.c1_eDir_slant
#print axioms Erdos634.Draft.TJCC1App3.c1_vertex_in_vertexSet
#print axioms Erdos634.Draft.TJCC1App3.c1_wall_cover_hyp_fails
#print axioms Erdos634.Draft.TJCC1App3.c1_antiparallel_hyp_fails_tile2
#print axioms Erdos634.Draft.TJCC1App3.c1_antiparallel_hyp_fails_tile3
#print axioms Erdos634.Draft.TJCC1App3.c1_T_junction_tile6
