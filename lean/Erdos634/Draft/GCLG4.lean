-- No sorry, no native_decide.
-- The pointwise G4 lemmas (`second_tile_at_edge_point`, `mem_dirSet`, `dirSet_sub`, `leftUnit_neg`, and the
-- global consequence `g4_final`) applied at an actual point X = (1/2, 1) of the hand-built bare `Dissection 3`
-- of TJCHand (T = (0,0),(4,0),(0,4) into P, Q, R; X lies in the open edge P.edge 2 = Q.edge 0 (reversed), a
-- genuinely interior non-vertex edge point).  Every hypothesis is proved from coordinates.  Two points where the
-- hypotheses fail are also checked: the T-vertex V = (1,2) (hypothesis `∀ i k, x ≠ pts` fails and the conclusion fails)
-- and the boundary point Y = (1,0) (not interior to the target: the conclusion "a second tile" fails).
import Erdos634.Draft.TJCHandApp

namespace Erdos634.Draft.GCLG4

open Erdos634.Geometry Erdos634.CertCoord Erdos634.Draft.TJCHelp Erdos634.Draft.TJCHand
  Erdos634.Draft.TJCHandApp

noncomputable def X : Plane := mkPt (1/2) 1

theorem hxv : X ∉ D.vertexSet := not_vertex _ _ (by
  intro p hp h; simp at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl <;> (have := Prod.mk.inj h; norm_num at this))

theorem hXint : X ∈ interior D.target.carrier :=
  T_interior (1/2) 1 (by norm_num) (by norm_num) (by norm_num)

theorem hX0 : X ∈ (D.tile 0).edge 2 := by
  have := mkPt_mem_segment 1 2 0 0 (1/2) (by norm_num) (by norm_num)
  have e : mkPt (1/2 : ℝ) 1 = mkPt ((1 - 1/2) * 1 + 1/2 * 0) ((1 - 1/2) * 2 + 1/2 * 0) := by norm_num
  show mkPt (1/2 : ℝ) 1 ∈ segment ℝ (mkPt 1 2) (mkPt 0 0)
  rw [e]; exact this

theorem hX1 : X ∈ (D.tile 1).edge 0 := by
  have := mkPt_mem_segment 0 0 1 2 (1/2) (by norm_num) (by norm_num)
  have e : mkPt (1/2 : ℝ) 1 = mkPt ((1 - 1/2) * 0 + 1/2 * 1) ((1 - 1/2) * 0 + 1/2 * 2) := by norm_num
  show mkPt (1/2 : ℝ) 1 ∈ segment ℝ (mkPt 0 0) (mkPt 1 2)
  rw [e]; exact this

/-- R = tile 2 lies in `{2x + y ≥ 4}`. -/
theorem R_ge : ∀ y ∈ (D.tile 2).carrier, 4 ≤ lin 2 1 y :=
  carrier_ge (D.tile 2) (f := lin 2 1) (c := 4) (by
    intro k; fin_cases k <;> simp [D_tile, tile, R] <;> norm_num)

/-- **The only edges of D through X** are P.edge 2 and Q.edge 0 (case analysis over all 9 (tile, edge)). -/
theorem edges_through (i k : Fin 3) (hx : mkPt (1/2 : ℝ) 1 ∈ (D.tile i).edge k) :
    (i = 0 ∧ k = 2) ∨ (i = 1 ∧ k = 0) := by
  have t2 : mkPt (1/2 : ℝ) 1 ∉ (D.tile 2).carrier := fun h => by
    have := R_ge _ h; rw [lin_mkPt] at this; norm_num at this
  fin_cases i <;> fin_cases k
  · exfalso
    have h : lin 0 1 (mkPt (1/2 : ℝ) 1) = 0 :=
      seg_eq (f := lin 0 1) (c := 0) (p := mkPt 0 0) (q := mkPt 2 0) (by norm_num) (by norm_num) hx
    rw [lin_mkPt] at h; norm_num at h
  · exfalso
    have h : lin 2 1 (mkPt (1/2 : ℝ) 1) = 4 :=
      seg_eq (f := lin 2 1) (c := 4) (p := mkPt 2 0) (q := mkPt 1 2) (by norm_num) (by norm_num) hx
    rw [lin_mkPt] at h; norm_num at h
  · left; exact ⟨rfl, rfl⟩
  · right; exact ⟨rfl, rfl⟩
  · exfalso
    have h : lin 2 1 (mkPt (1/2 : ℝ) 1) = 4 :=
      seg_eq (f := lin 2 1) (c := 4) (p := mkPt 1 2) (q := mkPt 0 4) (by norm_num) (by norm_num) hx
    rw [lin_mkPt] at h; norm_num at h
  · exfalso
    have h : lin 1 0 (mkPt (1/2 : ℝ) 1) = 0 :=
      seg_eq (f := lin 1 0) (c := 0) (p := mkPt 0 4) (q := mkPt 0 0) (by norm_num) (by norm_num) hx
    rw [lin_mkPt] at h; norm_num at h
  all_goals exact absurd ((D.tile 2).edge_subset_carrier _ hx) t2

/-! ## (1) `second_tile_at_edge_point` at X -/

theorem second_tile_at_X : ∃ i₁ : Fin 3, i₁ ≠ 0 ∧ OnEdge D X i₁ ∧ i₁ = 1 := by
  have hnv := D.notMem_vertexSet hxv
  obtain ⟨hz₀, hp₀⟩ := (D.tile 0).onEdge_data hX0 (hnv 0)
  obtain ⟨R, hR, hRt⟩ := Metric.isOpen_iff.mp isOpen_interior X hXint
  have hRt' : Metric.ball X R ⊆ D.target.carrier := hRt.trans interior_subset
  obtain ⟨i₁, hne, hi₁⟩ := D.second_tile_at_edge_point (by norm_num) hnv hR hRt' ⟨_, hz₀, hp₀⟩
  refine ⟨i₁, hne, hi₁, ?_⟩
  obtain ⟨m, hz, hp⟩ := hi₁
  have hxe := (D.tile i₁).mem_edge_of_coord_zero hz hp
  rcases edges_through i₁ _ hxe with ⟨h, _⟩ | ⟨h, _⟩
  · exact absurd h hne
  · exact h

/-! ## (2) `dirSet_sub` + `mem_dirSet` + `leftUnit_neg` at X -/

theorem neg_ne (d : Dir) : Dir.neg d ≠ d := by
  intro h
  have h1 : -d.1 = d.1 := congrArg Subtype.val h
  have h0 : d.1 = 0 := by
    have : d.1 + d.1 = 0 := by nth_rewrite 1 [← h1]; exact neg_add_cancel _
    have h2 : (2 : ℝ) • d.1 = 0 := by rw [two_smul]; exact this
    exact (smul_eq_zero.mp h2).resolve_left (by norm_num)
  have := d.2
  rw [h0, norm_zero] at this
  exact zero_ne_one this

/-- X lies in `dirSet d` for `d = P.leftUnit 2`; `dirSet_sub` puts it in `dirSet (neg d)`; the edge that carries
`neg d` through X is, by the enumeration `edges_through`, exactly Q.edge 0 (not P.edge 2, since `neg d ≠ d`). -/
theorem dirSet_sub_at_X :
    X ∈ D.dirSet ((D.tile 0).leftUnit 2) ∧ X ∈ D.dirSet (Dir.neg ((D.tile 0).leftUnit 2)) ∧
    (D.tile 1).leftUnit 0 = Dir.neg ((D.tile 0).leftUnit 2) := by
  have hd : X ∈ D.dirSet ((D.tile 0).leftUnit 2) :=
    ⟨Set.mem_iUnion.mpr ⟨0, Set.mem_iUnion.mpr ⟨2, Set.mem_iUnion.mpr ⟨rfl, hX0⟩⟩⟩, hXint⟩
  have h := D.dirSet_sub (by norm_num) _ ⟨hd, hxv⟩
  refine ⟨hd, h.1, ?_⟩
  obtain ⟨i, k, hk, hmem⟩ := D.mem_dirSet _ h.1
  rcases edges_through i k hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact absurd hk.symm (neg_ne _)
  · exact hk

/-! ## (3) `g4_final` at d = P.leftUnit 2: both sides have positive finite length -/

theorem dirSet_finite (d : Dir) :
    (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane) (D.dirSet d) ≠ ⊤ := by
  have hsub : D.dirSet d ⊆ ⋃ p : Fin 3 × Fin 3, (D.tile p.1).edge p.2 := by
    intro x hx
    obtain ⟨i, k, -, hmem⟩ := D.mem_dirSet d hx
    exact Set.mem_iUnion.mpr ⟨(i, k), hmem⟩
  refine ne_top_of_le_ne_top ?_ (MeasureTheory.measure_mono hsub)
  refine ne_top_of_le_ne_top ?_ (MeasureTheory.measure_iUnion_fintype_le _ _)
  refine (ENNReal.sum_lt_top.mpr fun p _ => ?_).ne
  show (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane) ((D.tile p.1).edge p.2) < ⊤
  rw [Tri.hausdorff_edge]; exact edist_lt_top _ _

/-- the segment X → (1,2) ⊆ interior target. -/
theorem seg_int : segment ℝ X (mkPt 1 2) ⊆ interior D.target.carrier := by
  have hc : Convex ℝ (interior D.target.carrier) := (D.target.convex).interior
  exact hc.segment_subset hXint (T_interior 1 2 (by norm_num) (by norm_num) (by norm_num))

theorem seg_P : segment ℝ X (mkPt 1 2) ⊆ (D.tile 0).edge 2 := by
  have hc : Convex ℝ ((D.tile 0).edge 2) := convex_segment _ _
  exact hc.segment_subset hX0 (left_mem_segment ℝ _ _)

theorem seg_Q : segment ℝ X (mkPt 1 2) ⊆ (D.tile 1).edge 0 := by
  have hc : Convex ℝ ((D.tile 1).edge 0) := convex_segment _ _
  exact hc.segment_subset hX1 (right_mem_segment ℝ _ _)

theorem edistX_pos : 0 < edist X (mkPt 1 2) := by
  rw [_root_.edist_pos]
  intro h
  have := mkPt_inj h; norm_num at this

/-- **`g4_final` at a concrete direction.**  For `d = P.leftUnit 2`, both `dirSet d` and `dirSet (neg d)` carry
strictly positive finite Hausdorff length (they contain the segment X→(1,2), length ≥ |X - (1,2)| > 0), and
`g4_final` says the two lengths are equal.  Non-vacuous: `d ≠ neg d`, both sets non-empty (X in both). -/
theorem g4_at_d :
    let d := (D.tile 0).leftUnit 2
    let μ : MeasureTheory.Measure Plane := MeasureTheory.Measure.hausdorffMeasure 1
    d ≠ Dir.neg d ∧ 0 < (μ (D.dirSet d)).toReal ∧ 0 < (μ (D.dirSet (Dir.neg d))).toReal ∧
    (μ (D.dirSet (Dir.neg d))).toReal = (μ (D.dirSet d)).toReal := by
  intro d μ
  have hseg : μ (segment ℝ X (mkPt 1 2)) = edist X (mkPt 1 2) := MeasureTheory.hausdorffMeasure_segment _ _
  have hdsub : segment ℝ X (mkPt 1 2) ⊆ D.dirSet d := fun y hy =>
    ⟨Set.mem_iUnion.mpr ⟨0, Set.mem_iUnion.mpr ⟨2, Set.mem_iUnion.mpr ⟨rfl, seg_P hy⟩⟩⟩, seg_int hy⟩
  have hnsub : segment ℝ X (mkPt 1 2) ⊆ D.dirSet (Dir.neg d) := fun y hy =>
    ⟨Set.mem_iUnion.mpr ⟨1, Set.mem_iUnion.mpr ⟨0, Set.mem_iUnion.mpr ⟨dirSet_sub_at_X.2.2, seg_Q hy⟩⟩⟩,
      seg_int hy⟩
  refine ⟨(neg_ne d).symm, ?_, ?_, D.g4_final (by norm_num) d⟩
  · refine ENNReal.toReal_pos ?_ (dirSet_finite d)
    exact (lt_of_lt_of_le (hseg ▸ edistX_pos) (MeasureTheory.measure_mono hdsub)).ne'
  · refine ENNReal.toReal_pos ?_ (dirSet_finite _)
    exact (lt_of_lt_of_le (hseg ▸ edistX_pos) (MeasureTheory.measure_mono hnsub)).ne'

/-! ## Negative controls -/

/-- At the T-vertex V = (1,2): the hypothesis `∀ i k, x ≠ pts` of `second_tile_at_edge_point` fails, and so does
its conclusion (the only tile with V in an open edge is R; no other tile is OnEdge). -/
theorem vertex_control :
    ¬ (∀ i k, mkPt (1 : ℝ) 2 ≠ (D.tile i).pts k) ∧
    OnEdge D (mkPt 1 2) 2 ∧ ¬ ∃ i₁ : Fin 3, i₁ ≠ 2 ∧ OnEdge D (mkPt 1 2) i₁ := by
  refine ⟨fun h => h 0 2 rfl, hand_T_junction_R, ?_⟩
  rintro ⟨i₁, hne, hi⟩
  fin_cases i₁
  · exact hand_antiparallel_hyp_fails_P hi
  · exact hand_antiparallel_hyp_fails_Q hi
  · exact hne rfl

/-- At the boundary point Y = (1,0) of P.edge 0 ⊆ T.edge 0: Y is not interior to the target
(`hxint` of `dirSet_sub` fails) and the "second tile" conclusion fails: no tile other than P has Y on an edge. -/
theorem boundary_control :
    mkPt (1 : ℝ) 0 ∉ interior D.target.carrier ∧
    ¬ ∃ i₁ : Fin 3, i₁ ≠ 0 ∧ OnEdge D (mkPt 1 0) i₁ := by
  have hY : mkPt (1 : ℝ) 0 ∈ (D.tile 0).edge 0 := by
    have := mkPt_mem_segment 0 0 2 0 (1/2) (by norm_num) (by norm_num)
    have e : mkPt (1 : ℝ) 0 = mkPt ((1 - 1/2) * 0 + 1/2 * 2) ((1 - 1/2) * 0 + 1/2 * 0) := by norm_num
    show mkPt (1 : ℝ) 0 ∈ segment ℝ (mkPt 0 0) (mkPt 2 0)
    rw [e]; exact this
  refine ⟨?_, ?_⟩
  · intro hint
    have hf : lin 0 1 ≠ 0 := lin_ne_zero (Or.inr (by norm_num))
    refine not_interior_on_line_ge hf (c := 0) (A := D.target.carrier) ?_ hint (by simp)
    exact carrier_ge T (f := lin 0 1) (c := 0) (by
      intro k; fin_cases k <;> simp [T] <;> norm_num)
  · rintro ⟨i₁, hne, ⟨m, hz, hp⟩⟩
    have hxe := (D.tile i₁).mem_edge_of_coord_zero hz hp
    have t2 : mkPt (1 : ℝ) 0 ∉ (D.tile 2).carrier := fun h => by
      have := R_ge _ h; rw [lin_mkPt] at this; norm_num at this
    obtain ⟨k, hk⟩ : ∃ k, mkPt (1 : ℝ) 0 ∈ (D.tile i₁).edge k := ⟨_, hxe⟩
    fin_cases i₁
    · exact hne rfl
    · fin_cases k
      · have h : lin 2 (-1) (mkPt (1 : ℝ) 0) = 0 :=
          seg_eq (f := lin 2 (-1)) (c := 0) (p := mkPt 0 0) (q := mkPt 1 2) (by norm_num) (by norm_num) hk
        rw [lin_mkPt] at h; norm_num at h
      · have h : lin 2 1 (mkPt (1 : ℝ) 0) = 4 :=
          seg_eq (f := lin 2 1) (c := 4) (p := mkPt 1 2) (q := mkPt 0 4) (by norm_num) (by norm_num) hk
        rw [lin_mkPt] at h; norm_num at h
      · have h : lin 1 0 (mkPt (1 : ℝ) 0) = 0 :=
          seg_eq (f := lin 1 0) (c := 0) (p := mkPt 0 4) (q := mkPt 0 0) (by norm_num) (by norm_num) hk
        rw [lin_mkPt] at h; norm_num at h
    · exact t2 ((D.tile 2).edge_subset_carrier _ hk)

end Erdos634.Draft.GCLG4

#print axioms Erdos634.Draft.GCLG4.second_tile_at_X
#print axioms Erdos634.Draft.GCLG4.dirSet_sub_at_X
#print axioms Erdos634.Draft.GCLG4.g4_at_d
#print axioms Erdos634.Draft.GCLG4.vertex_control
#print axioms Erdos634.Draft.GCLG4.boundary_control
