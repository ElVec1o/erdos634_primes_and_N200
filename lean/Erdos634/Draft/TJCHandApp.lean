-- No sorry, no native_decide.
-- Applications of the five pointwise lemmas to the hand-built T-junction dissection of TJCHand.
import Erdos634.Draft.TJCHand

namespace Erdos634.Draft.TJCHandApp

open Erdos634.Geometry Erdos634.CertCoord Erdos634.Draft.TJCHelp Erdos634.Draft.TJCHand

theorem detP : 0 < det3 0 0 2 0 1 2 := by norm_num [det3]
theorem detQ : 0 < det3 0 0 1 2 0 4 := by norm_num [det3]
theorem detR : 0 < det3 2 0 4 0 0 4 := by norm_num [det3]
theorem detT : 0 < det3 0 0 4 0 0 4 := by norm_num [det3]

theorem P_ld2 : P.leftDir 2 = mkPt (-1) (-2) := by
  unfold P; rw [leftDir_mkTri_pos _ _ _ _ _ _ _ detP]
  show mkPt 0 0 - mkPt 1 2 = _
  rw [mkPt_sub]; norm_num
theorem P_ld0 : P.leftDir 0 = mkPt 2 0 := by
  unfold P; rw [leftDir_mkTri_pos _ _ _ _ _ _ _ detP]
  show mkPt 2 0 - mkPt 0 0 = _
  rw [mkPt_sub]; norm_num
theorem Q_ld0 : Q.leftDir 0 = mkPt 1 2 := by
  unfold Q; rw [leftDir_mkTri_pos _ _ _ _ _ _ _ detQ]
  show mkPt 1 2 - mkPt 0 0 = _
  rw [mkPt_sub]; norm_num
theorem Q_ld2 : Q.leftDir 2 = mkPt 0 (-4) := by
  unfold Q; rw [leftDir_mkTri_pos _ _ _ _ _ _ _ detQ]
  show mkPt 0 0 - mkPt 0 4 = _
  rw [mkPt_sub]; norm_num
theorem T_ld0 : T.leftDir 0 = mkPt 4 0 := by
  unfold T; rw [leftDir_mkTri_pos _ _ _ _ _ _ _ detT]
  show mkPt 4 0 - mkPt 0 0 = _
  rw [mkPt_sub]; norm_num
theorem T_ld2 : T.leftDir 2 = mkPt 0 (-4) := by
  unfold T; rw [leftDir_mkTri_pos _ _ _ _ _ _ _ detT]
  show mkPt 0 0 - mkPt 0 4 = _
  rw [mkPt_sub]; norm_num

/-! ## (1) `leftDir_antiparallel` at the midpoint (1/2, 1) of the shared wall PQ -/

theorem hand_antiparallel :
    ∃ c : ℝ, c < 0 ∧ (D.tile 1).leftDir 0 = c • (D.tile 0).leftDir 2 ∧
      c = -1 ∧ (D.tile 1).leftDir 0 = mkPt 1 2 ∧ (D.tile 0).leftDir 2 = mkPt (-1) (-2) := by
  have hx0 : mkPt (1/2) 1 ∈ (D.tile 0).edge 2 := by
    have := mkPt_mem_segment 1 2 0 0 (1/2) (by norm_num) (by norm_num)
    have e : mkPt (1/2 : ℝ) 1 = mkPt ((1 - 1/2) * 1 + 1/2 * 0) ((1 - 1/2) * 2 + 1/2 * 0) := by norm_num
    rw [e]; exact this
  have hx1 : mkPt (1/2) 1 ∈ (D.tile 1).edge 0 := by
    have := mkPt_mem_segment 0 0 1 2 (1/2) (by norm_num) (by norm_num)
    have e : mkPt (1/2 : ℝ) 1 = mkPt ((1 - 1/2) * 0 + 1/2 * 1) ((1 - 1/2) * 0 + 1/2 * 2) := by norm_num
    rw [e]; exact this
  have n0a : mkPt (1/2 : ℝ) 1 ≠ (D.tile 0).pts 2 := fun h => by
    have := mkPt_inj h; norm_num at this
  have n0b : mkPt (1/2 : ℝ) 1 ≠ (D.tile 0).pts (2 + 1) := fun h => by
    have := mkPt_inj h; norm_num at this
  have n1a : mkPt (1/2 : ℝ) 1 ≠ (D.tile 1).pts 0 := fun h => by
    have := mkPt_inj h; norm_num at this
  have n1b : mkPt (1/2 : ℝ) 1 ≠ (D.tile 1).pts (0 + 1) := fun h => by
    have := mkPt_inj h; norm_num at this
  obtain ⟨hz0, hp0⟩ := (D.tile 0).onEdge_param hx0 n0a n0b
  obtain ⟨hz1, hp1⟩ := (D.tile 1).onEdge_param hx1 n1a n1b
  obtain ⟨c, hc, h⟩ := D.leftDir_antiparallel (i₁ := 0) (i₂ := 1) (by decide) hz0 hp0 hz1 hp1
  have h' : (D.tile 1).leftDir 0 = c • (D.tile 0).leftDir 2 := h
  have hQ : (D.tile 1).leftDir 0 = mkPt 1 2 := Q_ld0
  have hP : (D.tile 0).leftDir 2 = mkPt (-1) (-2) := P_ld2
  refine ⟨c, hc, h', ?_, hQ, hP⟩
  rw [hQ, hP, mkPt_smul] at h'
  have := mkPt_inj h'
  linarith [this.1]



/-! ## target barycentric coordinates -/

theorem T_coord (a b : ℝ) (k : Fin 3) : T.basis.coord k (mkPt a b) = ![1 - a/4 - b/4, a/4, b/4] k := by
  refine Erdos634.Subdivision.Tri.coord_eq_of_combo T _ _ ?_ ?_ k
  · simp; ring
  · show mkPt a b = _ • mkPt 0 0 + _ • mkPt 4 0 + _ • mkPt 0 4
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    rw [mkPt_smul, mkPt_smul, mkPt_smul, mkPt_add, mkPt_add]
    congr 1 <;> ring

theorem T_interior (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a + b < 4) :
    mkPt a b ∈ interior T.carrier := by
  apply interior_of_pos
  intro k
  rw [T_coord]
  fin_cases k <;> simp <;> linarith

/-- a point not equal to any of the five coordinate vertices is not in `vertexSet` -/
theorem not_vertex (a b : ℝ) (h : ∀ p ∈ ([(0,0), (2,0), (1,2), (0,4), (4,0)] : List (ℝ × ℝ)), (a, b) ≠ p) :
    mkPt a b ∉ D.vertexSet := by
  intro hmem
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hmem
  obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hi
  have hk' : mkPt a b = (D.tile i).pts k := by simpa using hk
  fin_cases i <;> fin_cases k <;>
  first
  | (have := mkPt_inj (hk' : mkPt a b = mkPt 0 0); exact h (0,0) (by simp) (by rw [this.1, this.2]))
  | (have := mkPt_inj (hk' : mkPt a b = mkPt 2 0); exact h (2,0) (by simp) (by rw [this.1, this.2]))
  | (have := mkPt_inj (hk' : mkPt a b = mkPt 1 2); exact h (1,2) (by simp) (by rw [this.1, this.2]))
  | (have := mkPt_inj (hk' : mkPt a b = mkPt 0 4); exact h (0,4) (by simp) (by rw [this.1, this.2]))
  | (have := mkPt_inj (hk' : mkPt a b = mkPt 4 0); exact h (4,0) (by simp) (by rw [this.1, this.2]))

theorem vtx_P (k : Fin 3) : ∃ a b : ℝ, (D.tile 0).pts k = mkPt a b := by
  fin_cases k <;> [exact ⟨0, 0, rfl⟩; exact ⟨2, 0, rfl⟩; exact ⟨1, 2, rfl⟩]

/-! ## (2) `wall_cover` on the wall PQ = open segment (0,0)-(1,2), line 2x - y = 0 -/

theorem hand_wall_cover :
    ∃ e ∈ D.lineChain (lin 2 (-1)) 0, mkPt (1/2) 1 ∈ (D.tile e.1).edge e.2 ∧
      e = ((1 : Fin 3), (0 : Fin 3)) := by
  have hf : lin 2 (-1) ≠ 0 := lin_ne_zero (Or.inl (by norm_num))
  have hu : mkPt 0 0 ≠ mkPt 1 2 := fun h => by have := mkPt_inj h; norm_num at this
  have hS : segment ℝ (mkPt 0 0) (mkPt 1 2) ⊆ {y | lin 2 (-1) y = 0} := by
    intro y hy
    exact seg_eq (f := lin 2 (-1)) (c := 0) (by simp) (by norm_num) hy
  have hopen : ∀ y ∈ openSegment ℝ (mkPt 0 0) (mkPt 1 2), ∃ b : ℝ, 0 < b ∧ b < 1 ∧ y = mkPt b (2 * b) := by
    intro y hy
    obtain ⟨a, b, ha, hb, hab, rfl⟩ := hy
    refine ⟨b, hb, by linarith, ?_⟩
    rw [mkPt_smul, mkPt_smul, mkPt_add]
    congr 1 <;> ring
  have hint : openSegment ℝ (mkPt 0 0) (mkPt 1 2) ⊆ interior D.target.carrier := by
    intro y hy
    obtain ⟨b, hb0, hb1, rfl⟩ := hopen y hy
    exact T_interior b (2 * b) hb0 (by linarith) (by linarith)
  have hwall : ∀ y ∈ openSegment ℝ (mkPt 0 0) (mkPt 1 2), ∀ i, y ∉ interior (D.tile i).carrier := by
    intro y hy i hyi
    have hfy : lin 2 (-1) y = 0 := hS (openSegment_subset_segment ℝ _ _ hy)
    obtain ⟨b, hb0, hb1, hyb⟩ := hopen y hy
    fin_cases i
    · refine not_interior_on_line_ge hf (c := 0) (A := (D.tile 0).carrier) ?_ hyi hfy
      refine carrier_ge (D.tile 0) (f := lin 2 (-1)) (c := 0) ?_
      intro k; fin_cases k <;> simp [D_tile, tile, P] <;> norm_num
    · refine not_interior_on_line hf (c := 0) (A := (D.tile 1).carrier) ?_ hyi hfy
      refine carrier_le (D.tile 1) (f := lin 2 (-1)) (c := 0) ?_
      intro k; fin_cases k <;> simp [D_tile, tile, Q] <;> norm_num
    · have h1 := carrier_ge (D.tile 2) (f := lin 2 1) (c := 4) (by
        intro k; fin_cases k <;> simp [D_tile, tile, R] <;> norm_num) y (interior_subset hyi)
      rw [hyb, lin_mkPt] at h1
      linarith
  have hx : mkPt (1/2 : ℝ) 1 ∈ openSegment ℝ (mkPt 0 0) (mkPt 1 2) := by
    have := mkPt_mem_openSegment 0 0 1 2 (1/2) (by norm_num) (by norm_num)
    have e : mkPt (1/2 : ℝ) 1 = mkPt ((1 - 1/2) * 0 + 1/2 * 1) ((1 - 1/2) * 0 + 1/2 * 2) := by norm_num
    rw [e]; exact this
  have hxv : mkPt (1/2 : ℝ) 1 ∉ D.vertexSet := not_vertex _ _ (by
    intro p hp h; simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl <;> (have := Prod.mk.inj h; norm_num at this))
  obtain ⟨e, he, hxe⟩ := D.wall_cover (lin 2 (-1)) 0 hf hu hS hint hwall hx hxv
  refine ⟨e, he, hxe, ?_⟩
  obtain ⟨i, k⟩ := e
  rw [Dissection.mem_lineChain] at he
  obtain ⟨h1, h2, h3⟩ := he
  simp only at h1 h2 h3
  fin_cases i
  · exfalso
    have h : lin 2 (-1) (mkPt 2 0) ≤ 0 := h3 1
    rw [lin_mkPt] at h; norm_num at h
  · fin_cases k
    · rfl
    · exfalso
      have h : lin 2 (-1) (mkPt 0 4) = 0 := h2
      rw [lin_mkPt] at h; norm_num at h
    · exfalso
      have h : lin 2 (-1) (mkPt 0 4) = 0 := h1
      rw [lin_mkPt] at h; norm_num at h
  · exfalso
    have h : lin 2 (-1) (mkPt 4 0) ≤ 0 := h3 1
    rw [lin_mkPt] at h; norm_num at h

/-! ## (3) `sameside_edges_subsingleton`: the two T-junction pieces P-edge1, Q-edge1 of R's long edge -/

theorem hand_sameside :
    ((D.tile 0).edge 1 ∩ (D.tile 1).edge 1).Subsingleton ∧ mkPt 1 2 ∈ (D.tile 0).edge 1 ∩ (D.tile 1).edge 1 := by
  have hf : lin 2 1 ≠ 0 := lin_ne_zero (Or.inl (by norm_num))
  have hne : ((0 : Fin 3), (1 : Fin 3)) ≠ ((1 : Fin 3), (1 : Fin 3)) := by decide
  have hle₁ : ∀ y ∈ (D.tile 0).carrier, lin 2 1 y ≤ 4 :=
    carrier_le (D.tile 0) (f := lin 2 1) (c := 4) (by
      intro k; fin_cases k <;> simp [D_tile, tile, P] <;> norm_num)
  have hle₂ : ∀ y ∈ (D.tile 1).carrier, lin 2 1 y ≤ 4 :=
    carrier_le (D.tile 1) (f := lin 2 1) (c := 4) (by
      intro k; fin_cases k <;> simp [D_tile, tile, Q] <;> norm_num)
  have hE₁ : ∀ y ∈ (D.tile 0).edge 1, lin 2 1 y = 4 := by
    intro y hy
    exact seg_eq (f := lin 2 1) (c := 4) (p := mkPt 2 0) (q := mkPt 1 2) (by norm_num) (by norm_num) hy
  have hE₂ : ∀ y ∈ (D.tile 1).edge 1, lin 2 1 y = 4 := by
    intro y hy
    exact seg_eq (f := lin 2 1) (c := 4) (p := mkPt 1 2) (q := mkPt 0 4) (by norm_num) (by norm_num) hy
  have hsub := D.sameside_edges_subsingleton (lin 2 1) 4 hf hne hle₁ hle₂ hE₁ hE₂
  exact ⟨hsub,
    (show mkPt 1 2 ∈ (D.tile 0).edge 1 from right_mem_segment ℝ _ _),
    (show mkPt 1 2 ∈ (D.tile 1).edge 1 from left_mem_segment ℝ _ _)⟩

/-- Failure of the hypotheses of (3): R's edge 2 lies on the same line `2x + y = 4` but R is on the other side, so
`hle₂` fails (R has the vertex (4,0) with value 8), and indeed the conclusion fails: P-edge1 ∩ R-edge2 contains
two distinct points (2,0) and (1,2). -/
theorem hand_sameside_negative :
    ¬ (∀ y ∈ (D.tile 2).carrier, lin 2 1 y ≤ 4) ∧
    ¬ ((D.tile 0).edge 1 ∩ (D.tile 2).edge 2).Subsingleton := by
  constructor
  · intro h
    have hv : mkPt 4 0 ∈ (D.tile 2).carrier := subset_convexHull ℝ _ ⟨1, rfl⟩
    have := h _ hv
    rw [lin_mkPt] at this; norm_num at this
  · intro h
    have a1 : mkPt 2 0 ∈ (D.tile 0).edge 1 ∩ (D.tile 2).edge 2 :=
      ⟨(show mkPt 2 0 ∈ (D.tile 0).edge 1 from left_mem_segment ℝ _ _),
       (show mkPt 2 0 ∈ (D.tile 2).edge 2 from right_mem_segment ℝ _ _)⟩
    have a2 : mkPt 1 2 ∈ (D.tile 0).edge 1 ∩ (D.tile 2).edge 2 := by
      refine ⟨(show mkPt 1 2 ∈ (D.tile 0).edge 1 from right_mem_segment ℝ _ _), ?_⟩
      have := mkPt_mem_segment 0 4 2 0 (1/2) (by norm_num) (by norm_num)
      have e : mkPt (1 : ℝ) 2 = mkPt ((1 - 1/2) * 0 + 1/2 * 2) ((1 - 1/2) * 4 + 1/2 * 0) := by norm_num
      show mkPt 1 2 ∈ segment ℝ (mkPt 0 4) (mkPt 2 0)
      rw [e]; exact this
    have := mkPt_inj (h a1 a2)
    norm_num at this

/-! ## (4) `edge_interior_or_side`, interior case (x = (3/2, 1) on P's edge 1) and side case (x = (1,0) on P's edge 0) -/

theorem hand_eios_interior :
    mkPt (3/2) 1 ∈ interior D.target.carrier := by
  have hx : mkPt (3/2 : ℝ) 1 ∈ D.eSet ((0 : Fin 3), (1 : Fin 3)) := by
    have := mkPt_mem_segment 2 0 1 2 (1/2) (by norm_num) (by norm_num)
    have e : mkPt (3/2 : ℝ) 1 = mkPt ((1 - 1/2) * 2 + 1/2 * 1) ((1 - 1/2) * 0 + 1/2 * 2) := by norm_num
    show mkPt (3/2 : ℝ) 1 ∈ segment ℝ (mkPt 2 0) (mkPt 1 2)
    rw [e]; exact this
  have h1 : mkPt (3/2 : ℝ) 1 ≠ (D.tile ((0 : Fin 3), (1 : Fin 3)).1).pts ((0 : Fin 3), (1 : Fin 3)).2 :=
    fun h => by have := mkPt_inj h; norm_num at this
  have h2 : mkPt (3/2 : ℝ) 1 ≠ (D.tile ((0 : Fin 3), (1 : Fin 3)).1).pts (((0 : Fin 3), (1 : Fin 3)).2 + 1) :=
    fun h => by have := mkPt_inj h; norm_num at this
  rcases D.edge_interior_or_side _ hx h1 h2 with h | ⟨j, hj⟩
  · exact h
  · exfalso
    -- the whole edge (2,0)-(1,2) would lie on a target side; (1,2) is on none
    have hp : mkPt 1 2 ∈ D.target.edge j := hj (show mkPt 1 2 ∈ (D.tile 0).edge 1 from right_mem_segment ℝ _ _)
    fin_cases j
    · have := seg_eq (f := lin 0 1) (c := 0) (p := mkPt 0 0) (q := mkPt 4 0) (by norm_num) (by norm_num) hp
      rw [lin_mkPt] at this; norm_num at this
    · have := seg_eq (f := lin 1 1) (c := 4) (p := mkPt 4 0) (q := mkPt 0 4) (by norm_num) (by norm_num) hp
      rw [lin_mkPt] at this; norm_num at this
    · have := seg_eq (f := lin 1 0) (c := 0) (p := mkPt 0 4) (q := mkPt 0 0) (by norm_num) (by norm_num) hp
      rw [lin_mkPt] at this; norm_num at this

theorem hand_eios_side :
    ∃ j : Fin 3, D.eSet ((0 : Fin 3), (0 : Fin 3)) ⊆ D.target.edge j ∧ j = 0 := by
  have hx : mkPt (1 : ℝ) 0 ∈ D.eSet ((0 : Fin 3), (0 : Fin 3)) := by
    have := mkPt_mem_segment 0 0 2 0 (1/2) (by norm_num) (by norm_num)
    have e : mkPt (1 : ℝ) 0 = mkPt ((1 - 1/2) * 0 + 1/2 * 2) ((1 - 1/2) * 0 + 1/2 * 0) := by norm_num
    show mkPt (1 : ℝ) 0 ∈ segment ℝ (mkPt 0 0) (mkPt 2 0)
    rw [e]; exact this
  have h1 : mkPt (1 : ℝ) 0 ≠ (D.tile ((0 : Fin 3), (0 : Fin 3)).1).pts ((0 : Fin 3), (0 : Fin 3)).2 :=
    fun h => by have := mkPt_inj h; norm_num at this
  have h2 : mkPt (1 : ℝ) 0 ≠ (D.tile ((0 : Fin 3), (0 : Fin 3)).1).pts (((0 : Fin 3), (0 : Fin 3)).2 + 1) :=
    fun h => by have := mkPt_inj h; norm_num at this
  rcases D.edge_interior_or_side _ hx h1 h2 with h | ⟨j, hj⟩
  · exfalso
    have hy := carrier_ge T (f := lin 0 1) (c := 0) (by
      intro k; fin_cases k <;> simp [T])
    exact not_interior_on_line_ge (lin_ne_zero (Or.inr (by norm_num))) (c := 0) (A := T.carrier) hy h
      (by simp)
  · refine ⟨j, hj, ?_⟩
    have p0 : mkPt 0 0 ∈ D.target.edge j := hj (show mkPt 0 0 ∈ (D.tile 0).edge 0 from left_mem_segment ℝ _ _)
    have p2 : mkPt 2 0 ∈ D.target.edge j := hj (show mkPt 2 0 ∈ (D.tile 0).edge 0 from right_mem_segment ℝ _ _)
    fin_cases j
    · rfl
    · exfalso
      have := seg_eq (f := lin 1 1) (c := 4) (p := mkPt 4 0) (q := mkPt 0 4) (by norm_num) (by norm_num) p0
      rw [lin_mkPt] at this; norm_num at this
    · exfalso
      have := seg_eq (f := lin 1 0) (c := 0) (p := mkPt 0 4) (q := mkPt 0 0) (by norm_num) (by norm_num) p2
      rw [lin_mkPt] at this; norm_num at this

/-! ## (5) `eDir_of_side`: P's base edge on target side 0, Q's left edge on target side 2 -/

theorem P_lu0 : (P.leftUnit 0).1 = mkPt 1 0 := by
  show ‖P.leftDir 0‖⁻¹ • P.leftDir 0 = _
  rw [P_ld0, norm_mkPt_x, mkPt_smul]; norm_num

theorem T_lu0 : (T.leftUnit 0).1 = mkPt 1 0 := by
  show ‖T.leftDir 0‖⁻¹ • T.leftDir 0 = _
  rw [T_ld0, norm_mkPt_x, mkPt_smul]; norm_num

theorem Q_lu2 : (Q.leftUnit 2).1 = mkPt 0 (-1) := by
  show ‖Q.leftDir 2‖⁻¹ • Q.leftDir 2 = _
  rw [Q_ld2, norm_mkPt_y, mkPt_smul]; norm_num

theorem T_lu2 : (T.leftUnit 2).1 = mkPt 0 (-1) := by
  show ‖T.leftDir 2‖⁻¹ • T.leftDir 2 = _
  rw [T_ld2, norm_mkPt_y, mkPt_smul]; norm_num

theorem hand_eDir_base :
    D.eDir ((0 : Fin 3), (0 : Fin 3)) = D.target.leftUnit 0 ∧
    (D.eDir ((0 : Fin 3), (0 : Fin 3))).1 = mkPt 1 0 := by
  have hh : D.eSet ((0 : Fin 3), (0 : Fin 3)) ⊆ D.target.edge 0 := by
    have hc := convex_segment (𝕜 := ℝ) (mkPt 0 0) (mkPt 4 0)
    have hm : mkPt (2 : ℝ) 0 ∈ segment ℝ (mkPt 0 0) (mkPt 4 0) := by
      have := mkPt_mem_segment 0 0 4 0 (1/2) (by norm_num) (by norm_num)
      have e : mkPt (2 : ℝ) 0 = mkPt ((1 - 1/2) * 0 + 1/2 * 4) ((1 - 1/2) * 0 + 1/2 * 0) := by norm_num
      rw [e]; exact this
    exact hc.segment_subset (left_mem_segment ℝ _ _) hm
  exact ⟨D.eDir_of_side hh, P_lu0⟩

theorem hand_eDir_left :
    D.eDir ((1 : Fin 3), (2 : Fin 3)) = D.target.leftUnit 2 ∧
    (D.eDir ((1 : Fin 3), (2 : Fin 3))).1 = mkPt 0 (-1) := by
  have hh : D.eSet ((1 : Fin 3), (2 : Fin 3)) ⊆ D.target.edge 2 := fun y hy => hy
  exact ⟨D.eDir_of_side hh, Q_lu2⟩

/-! ## negative controls: the T-vertex (1,2) -/

theorem hand_vertex_in_vertexSet : mkPt 1 2 ∈ D.vertexSet :=
  Set.mem_iUnion.mpr ⟨0, Set.mem_iUnion.mpr ⟨2, rfl⟩⟩

/-- the hypothesis `x ∉ vertexSet` of `wall_cover` fails at the T-vertex -/
theorem hand_wall_cover_hyp_fails : ¬ (mkPt (1 : ℝ) 2 ∉ D.vertexSet) := fun h => h hand_vertex_in_vertexSet

/-- the `OnEdge` data of `leftDir_antiparallel` fails at the T-vertex for the tiles that have it as a vertex -/
theorem hand_antiparallel_hyp_fails_P : ¬ OnEdge D (mkPt 1 2) 0 := vertex_not_onEdge D 0 2
theorem hand_antiparallel_hyp_fails_Q : ¬ OnEdge D (mkPt 1 2) 1 := vertex_not_onEdge D 1 1

/-- ... while the third tile R does carry (1,2) in its open edge (the T-junction): `OnEdge D (1,2) 2` holds -/
theorem hand_T_junction_R : OnEdge D (mkPt 1 2) 2 := by
  have hx : mkPt (1 : ℝ) 2 ∈ (D.tile 2).edge 2 := by
    have := mkPt_mem_segment 0 4 2 0 (1/2) (by norm_num) (by norm_num)
    have e : mkPt (1 : ℝ) 2 = mkPt ((1 - 1/2) * 0 + 1/2 * 2) ((1 - 1/2) * 4 + 1/2 * 0) := by norm_num
    show mkPt 1 2 ∈ segment ℝ (mkPt 0 4) (mkPt 2 0)
    rw [e]; exact this
  have h1 : mkPt (1 : ℝ) 2 ≠ (D.tile 2).pts 2 := fun h => by have := mkPt_inj h; norm_num at this
  have h2 : mkPt (1 : ℝ) 2 ≠ (D.tile 2).pts (2 + 1) := fun h => by have := mkPt_inj h; norm_num at this
  obtain ⟨hz, hp⟩ := (D.tile 2).onEdge_param hx h1 h2
  exact ⟨2 + 2, hz, hp⟩

end Erdos634.Draft.TJCHandApp

#print axioms Erdos634.Draft.TJCHandApp.hand_antiparallel
#print axioms Erdos634.Draft.TJCHandApp.hand_wall_cover
#print axioms Erdos634.Draft.TJCHandApp.hand_sameside
#print axioms Erdos634.Draft.TJCHandApp.hand_sameside_negative
#print axioms Erdos634.Draft.TJCHandApp.hand_eios_interior
#print axioms Erdos634.Draft.TJCHandApp.hand_eios_side
#print axioms Erdos634.Draft.TJCHandApp.hand_eDir_base
#print axioms Erdos634.Draft.TJCHandApp.hand_eDir_left
#print axioms Erdos634.Draft.TJCHandApp.hand_wall_cover_hyp_fails
#print axioms Erdos634.Draft.TJCHandApp.hand_antiparallel_hyp_fails_P
#print axioms Erdos634.Draft.TJCHandApp.hand_antiparallel_hyp_fails_Q
#print axioms Erdos634.Draft.TJCHandApp.hand_T_junction_R
