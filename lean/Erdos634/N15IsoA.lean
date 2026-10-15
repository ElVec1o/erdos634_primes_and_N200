import Erdos634.CertNode

/-!
# N=15 isoA: no `CongruentDissection` of the target [('0', '0'), ('15', '0'), ('15/2', '45/2')] by the tile (4, 15, 16)

Generated file, do not edit.  Unpruned exhaustive tree with 10 nodes, no riders.  Every node is a
theorem about an arbitrary `CongruentDissection`; root `node_0` concludes `False`.

No `sorry`; standard axioms.
-/

set_option maxHeartbeats 4000000

namespace Erdos634.N15IsoA

open Erdos634.Geometry Erdos634.CertCoord Erdos634.CertGeom Erdos634.PlacementCompleteness
  Erdos634.SixPlacements Erdos634.CertNode

theorem hD7 : (0:ℝ) < 7 := by norm_num
theorem sr7_lt : sr 7 < 3 := sr_lt hD7 (by norm_num) (by norm_num)
theorem sr7_gt1 : 1 < sr 7 := sr_gt hD7 (by norm_num) (by norm_num)

theorem TGT_pos : 0 < ef 0 0 15 0 (15/2) (45/2) := by unfold ef; norm_num
/-- The target `(0, 0)`, `(15, 0)`, `(15/2, 45/2·r)`. -/
noncomputable def TGT : Tri := rtri 7 hD7 0 0 15 0 (15/2) (45/2) TGT_pos
theorem MODEL_pos : 0 < ef 0 0 4 0 (47/8) (45/8) := by unfold ef; norm_num
/-- The model tile `(0, 0)`, `(4, 0)`, `(47/8, 45/8·r)`: sides `4, 15, 16`. -/
noncomputable def MODEL : Tri := rtri 7 hD7 0 0 4 0 (47/8) (45/8) MODEL_pos
theorem MODEL_sides : dist (MODEL.pts 0) (MODEL.pts 1) = 4 ∧ dist (MODEL.pts 1) (MODEL.pts 2) = 15 ∧
    dist (MODEL.pts 0) (MODEL.pts 2) = 16 :=
  model_sides_rp hD7 MODEL_pos (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem T0_pos : 0 < ef 0 0 4 0 (47/8) (45/8) := by unfold ef; norm_num
/-- `T0` = `(0, 0)`, `(4, 0)`, `(47/8, 45/8·r)`. -/
noncomputable def T0 : Tri := rtri 7 hD7 0 0 4 0 (47/8) (45/8) T0_pos
theorem T0_pts : T0.pts 0 = rp 7 0 0 ∧ T0.pts 1 = rp 7 4 0 ∧ T0.pts 2 = rp 7 (47/8) (45/8) := ⟨rfl, rfl, rfl⟩

theorem T1_pos : 0 < ef 0 0 (47/8) (45/8) (15/8) (45/8) := by unfold ef; norm_num
/-- `T1` = `(0, 0)`, `(47/8, 45/8·r)`, `(15/8, 45/8·r)`. -/
noncomputable def T1 : Tri := rtri 7 hD7 0 0 (47/8) (45/8) (15/8) (45/8) T1_pos
theorem T1_pts : T1.pts 0 = rp 7 0 0 ∧ T1.pts 1 = rp 7 (47/8) (45/8) ∧ T1.pts 2 = rp 7 (15/8) (45/8) := ⟨rfl, rfl, rfl⟩

theorem T2_pos : 0 < ef 4 0 8 0 (79/8) (45/8) := by unfold ef; norm_num
/-- `T2` = `(4, 0)`, `(8, 0)`, `(79/8, 45/8·r)`. -/
noncomputable def T2 : Tri := rtri 7 hD7 4 0 8 0 (79/8) (45/8) T2_pos
theorem T2_pts : T2.pts 0 = rp 7 4 0 ∧ T2.pts 1 = rp 7 8 0 ∧ T2.pts 2 = rp 7 (79/8) (45/8) := ⟨rfl, rfl, rfl⟩

theorem T3_pos : 0 < ef 4 0 (79/8) (45/8) (47/8) (45/8) := by unfold ef; norm_num
/-- `T3` = `(4, 0)`, `(79/8, 45/8·r)`, `(47/8, 45/8·r)`. -/
noncomputable def T3 : Tri := rtri 7 hD7 4 0 (79/8) (45/8) (47/8) (45/8) T3_pos
theorem T3_pts : T3.pts 0 = rp 7 4 0 ∧ T3.pts 1 = rp 7 (79/8) (45/8) ∧ T3.pts 2 = rp 7 (47/8) (45/8) := ⟨rfl, rfl, rfl⟩

theorem T4_pos : 0 < ef 8 0 12 0 (49/8) (45/8) := by unfold ef; norm_num
/-- `T4` = `(8, 0)`, `(12, 0)`, `(49/8, 45/8·r)`. -/
noncomputable def T4 : Tri := rtri 7 hD7 8 0 12 0 (49/8) (45/8) T4_pos
theorem T4_pts : T4.pts 0 = rp 7 8 0 ∧ T4.pts 1 = rp 7 12 0 ∧ T4.pts 2 = rp 7 (49/8) (45/8) := ⟨rfl, rfl, rfl⟩

theorem T5_pos : 0 < ef 4 0 (1217/128) (675/128) 6 6 := by unfold ef; norm_num
/-- `T5` = `(4, 0)`, `(1217/128, 675/128·r)`, `(6, 6·r)`. -/
noncomputable def T5 : Tri := rtri 7 hD7 4 0 (1217/128) (675/128) 6 6 T5_pos
theorem T5_pts : T5.pts 0 = rp 7 4 0 ∧ T5.pts 1 = rp 7 (1217/128) (675/128) ∧ T5.pts 2 = rp 7 6 6 := ⟨rfl, rfl, rfl⟩

theorem T6_pos : 0 < ef 4 0 (79/8) (45/8) (2209/2048) (2115/2048) := by unfold ef; norm_num
/-- `T6` = `(4, 0)`, `(79/8, 45/8·r)`, `(2209/2048, 2115/2048·r)`. -/
noncomputable def T6 : Tri := rtri 7 hD7 4 0 (79/8) (45/8) (2209/2048) (2115/2048) T6_pos
theorem T6_pts : T6.pts 0 = rp 7 4 0 ∧ T6.pts 1 = rp 7 (79/8) (45/8) ∧ T6.pts 2 = rp 7 (2209/2048) (2115/2048) := ⟨rfl, rfl, rfl⟩

theorem T7_pos : 0 < ef 4 0 (1217/128) (675/128) (1/8) (3/8) := by unfold ef; norm_num
/-- `T7` = `(4, 0)`, `(1217/128, 675/128·r)`, `(1/8, 3/8·r)`. -/
noncomputable def T7 : Tri := rtri 7 hD7 4 0 (1217/128) (675/128) (1/8) (3/8) T7_pos
theorem T7_pts : T7.pts 0 = rp 7 4 0 ∧ T7.pts 1 = rp 7 (1217/128) (675/128) ∧ T7.pts 2 = rp 7 (1/8) (3/8) := ⟨rfl, rfl, rfl⟩

theorem T8_pos : 0 < ef 4 0 8 0 (17/8) (45/8) := by unfold ef; norm_num
/-- `T8` = `(4, 0)`, `(8, 0)`, `(17/8, 45/8·r)`. -/
noncomputable def T8 : Tri := rtri 7 hD7 4 0 8 0 (17/8) (45/8) T8_pos
theorem T8_pts : T8.pts 0 = rp 7 4 0 ∧ T8.pts 1 = rp 7 8 0 ∧ T8.pts 2 = rp 7 (17/8) (45/8) := ⟨rfl, rfl, rfl⟩

theorem T9_pos : 0 < ef 0 0 (705/128) (675/128) 2 6 := by unfold ef; norm_num
/-- `T9` = `(0, 0)`, `(705/128, 675/128·r)`, `(2, 6·r)`. -/
noncomputable def T9 : Tri := rtri 7 hD7 0 0 (705/128) (675/128) 2 6 T9_pos
theorem T9_pts : T9.pts 0 = rp 7 0 0 ∧ T9.pts 1 = rp 7 (705/128) (675/128) ∧ T9.pts 2 = rp 7 2 6 := ⟨rfl, rfl, rfl⟩

/-- Node 4: 4 placed tile(s), `v = (8, 0)`, `d = (1, 0)`; kills: escape(Q, edge 1), escape(P, edge 1), overlap(tile 2), escape(P, edge 1), escape(Q, edge 1), escape(Q, edge 1). -/
theorem node_4 {N : ℕ} (D : CongruentDissection N)
    (htarget : D.target.carrier = TGT.carrier) (hmodel : D.model.Congruent MODEL)
    (i0 i1 i2 i3 : Fin N) (h0 : (D.tile i0).carrier = T0.carrier) (h1 : (D.tile i1).carrier = T1.carrier) (h2 : (D.tile i2).carrier = T2.carrier) (h3 : (D.tile i3).carrier = T3.carrier)
    : False := by
  classical
  have hyT : ∀ p ∈ TGT.carrier, 0 ≤ p 1 := fun p hp => target_y_nonneg hD7 (by norm_num) TGT_pos hp
  have hU : ∀ p, p ∈ unfilled D.toDissection ([i0, i1, i2, i3] : List (Fin N)).toFinset ↔ p ∈ TGT.carrier ∧ p ∉ T0.carrier ∧ p ∉ T1.carrier ∧ p ∉ T2.carrier ∧ p ∉ T3.carrier := by
    intro p; rw [mem_unfilled_iff, htarget]
    simp [h0, h1, h2, h3]
  have hlex : ∀ p ∈ closure (unfilled D.toDissection ([i0, i1, i2, i3] : List (Fin N)).toFinset), LexLE (rp 7 8 0) p := by
    refine hlex_of D.toDissection _ _ ((TGT.carrier ∩ halfR 7 0 1 0) ∩ (halfR 7 1 0 (-8) ∪ ((halfR 7 (-45/8) (15/8) (45/2) ∩ (halfR 7 (-45/8) (47/8) 0 ∩ (halfR 7 0 4 (-45/2)))) ∪ ((halfR 7 (45/8) (-15/8) (-45/2) ∩ (halfR 7 (45/8) (-47/8) 0 ∩ (halfR 7 (-45/8) (47/8) 0))) ∪ ((halfR 7 (45/8) (-15/8) (-45/2) ∩ (halfR 7 (45/8) (-47/8) 0 ∩ (halfR 7 (45/8) (-47/8) 0 ∩ (halfR 7 0 4 (-45/2))))) ∪ ((halfR 7 (45/8) (-15/8) (-45/2) ∩ (halfR 7 (-45/8) (47/8) 0)))))))) ((TGT.isCompact.isClosed.inter (isClosed_halfR _ _ _ _)).inter ((isClosed_halfR _ _ _ _).union (((isClosed_halfR _ _ _ _).inter ((isClosed_halfR _ _ _ _).inter (isClosed_halfR _ _ _ _))).union (((isClosed_halfR _ _ _ _).inter ((isClosed_halfR _ _ _ _).inter (isClosed_halfR _ _ _ _))).union (((isClosed_halfR _ _ _ _).inter ((isClosed_halfR _ _ _ _).inter ((isClosed_halfR _ _ _ _).inter (isClosed_halfR _ _ _ _)))).union ((isClosed_halfR _ _ _ _).inter (isClosed_halfR _ _ _ _))))))) ?_ ?_
    · intro p hpT hnot
      obtain ⟨X, Y, rfl⟩ := exists_rp hD7 p
      have hpT' : rp 7 X Y ∈ TGT.carrier := htarget ▸ hpT
      obtain ⟨hT0, hT1, hT2⟩ := rtri_ef_nonneg hD7 TGT_pos hpT'
      unfold ef at hT0 hT1 hT2
      have hn0 : ¬ (0 ≤ 0 * X + 4 * Y + 0 ∧ 0 ≤ (-45/8) * X + (15/8) * Y + (45/2) ∧ 0 ≤ (45/8) * X + (-47/8) * Y + 0) := fun h =>
        hnot i0 (by simp) (by rw [h0]; exact mem_rtri hD7 T0_pos (by unfold ef; linarith [h.1]) (by unfold ef; linarith [h.2.1]) (by unfold ef; linarith [h.2.2]))
      have hn1 : ¬ (0 ≤ (-45/8) * X + (47/8) * Y + 0 ∧ 0 ≤ 0 * X + (-4) * Y + (45/2) ∧ 0 ≤ (45/8) * X + (-15/8) * Y + 0) := fun h =>
        hnot i1 (by simp) (by rw [h1]; exact mem_rtri hD7 T1_pos (by unfold ef; linarith [h.1]) (by unfold ef; linarith [h.2.1]) (by unfold ef; linarith [h.2.2]))
      have hn2 : ¬ (0 ≤ 0 * X + 4 * Y + 0 ∧ 0 ≤ (-45/8) * X + (15/8) * Y + 45 ∧ 0 ≤ (45/8) * X + (-47/8) * Y + (-45/2)) := fun h =>
        hnot i2 (by simp) (by rw [h2]; exact mem_rtri hD7 T2_pos (by unfold ef; linarith [h.1]) (by unfold ef; linarith [h.2.1]) (by unfold ef; linarith [h.2.2]))
      have hn3 : ¬ (0 ≤ (-45/8) * X + (47/8) * Y + (45/2) ∧ 0 ≤ 0 * X + (-4) * Y + (45/2) ∧ 0 ≤ (45/8) * X + (-15/8) * Y + (-45/2)) := fun h =>
        hnot i3 (by simp) (by rw [h3]; exact mem_rtri hD7 T3_pos (by unfold ef; linarith [h.1]) (by unfold ef; linarith [h.2.1]) (by unfold ef; linarith [h.2.2]))
      have hY : 0 ≤ Y := by
        by_contra hR; push_neg at hR
        linarith
      simp only [Set.mem_inter_iff, Set.mem_union, mem_halfR_rp hD7]
      refine ⟨⟨hpT', by linarith⟩, ?_⟩
      rcases le_or_gt 8 X with hX | hX
      · exact Or.inl (by linarith)
      · -- the region X < xv, Y ≥ yv
        rcases le_or_gt 0 ((-45/8) * X + (15/8) * Y + (45/2)) with hg | hg
        · -- 0 ≤ (-45/8) * X + (15/8) * Y + (45/2)
          rcases le_or_gt 0 ((45/8) * X + (-47/8) * Y + 0) with hg | hg
          · -- 0 ≤ (45/8) * X + (-47/8) * Y + 0
            exact (hn0 ⟨by linarith, by linarith, by linarith⟩).elim
          · -- (45/8) * X + (-47/8) * Y + 0 < 0
            rcases le_or_gt 0 (0 * X + (-4) * Y + (45/2)) with hg | hg
            · -- 0 ≤ 0 * X + (-4) * Y + (45/2)
              exact (hn1 ⟨by linarith, by linarith, by linarith⟩).elim
            · -- 0 * X + (-4) * Y + (45/2) < 0
              exact Or.inr (Or.inl ⟨by linarith, by linarith, by linarith⟩)
        · -- (-45/8) * X + (15/8) * Y + (45/2) < 0
          rcases le_or_gt 0 ((45/8) * X + (-47/8) * Y + 0) with hg | hg
          · -- 0 ≤ (45/8) * X + (-47/8) * Y + 0
            rcases le_or_gt 0 ((-45/8) * X + (47/8) * Y + 0) with hg | hg
            · -- 0 ≤ (-45/8) * X + (47/8) * Y + 0
              exact Or.inr (Or.inr (Or.inl ⟨by linarith, by linarith, by linarith⟩))
            · -- (-45/8) * X + (47/8) * Y + 0 < 0
              rcases le_or_gt 0 (0 * X + (-4) * Y + (45/2)) with hg | hg
              · -- 0 ≤ 0 * X + (-4) * Y + (45/2)
                rcases le_or_gt 0 ((45/8) * X + (-47/8) * Y + (-45/2)) with hg | hg
                · -- 0 ≤ (45/8) * X + (-47/8) * Y + (-45/2)
                  exact (hn2 ⟨by linarith, by linarith, by linarith⟩).elim
                · -- (45/8) * X + (-47/8) * Y + (-45/2) < 0
                  exact (hn3 ⟨by linarith, by linarith, by linarith⟩).elim
              · -- 0 * X + (-4) * Y + (45/2) < 0
                exact Or.inr (Or.inr (Or.inr (Or.inl ⟨by linarith, by linarith, by linarith, by linarith⟩)))
          · -- (45/8) * X + (-47/8) * Y + 0 < 0
            exact Or.inr (Or.inr (Or.inr (Or.inr (⟨by linarith, by linarith⟩))))
    · intro p hp
      obtain ⟨X, Y, rfl⟩ := exists_rp hD7 p
      simp only [Set.mem_inter_iff, Set.mem_union, mem_halfR_rp hD7] at hp
      obtain ⟨⟨hpT, hY⟩, hdis⟩ := hp
      obtain ⟨hT0, hT1, hT2⟩ := rtri_ef_nonneg hD7 TGT_pos hpT
      unfold ef at hT0 hT1 hT2
      refine lexLE_rp hD7 (by linarith) (fun hYe => ?_)
      rcases hdis with h | ⟨c0, c1, c2⟩ | ⟨c0, c1, c2⟩ | ⟨c0, c1, c2, c3⟩ | ⟨c0, c1⟩ <;> linarith
  have hfree : ∀ ε : ℝ, 0 < ε → ∃ t s : ℝ, 0 < t ∧ t < ε ∧ 0 < s ∧ s < ε ∧
      rp 7 8 0 + t • (rp 7 1 0 + s • perp (rp 7 1 0)) ∈ unfilled D.toDissection ([i0, i1, i2, i3] : List (Fin N)).toFinset := by
    refine hfree_of hD7 (B := 3) (by norm_num) sr7_lt (τ := (1/4)) (by norm_num) _ _ _ ?_
    intro t ht htτ
    rw [pt_ccw_rp 7 hD7, hU]
    have ht2 : t ^ 2 ≤ (1/4) * t := by nlinarith [mul_le_mul_of_nonneg_left htτ ht.le]
    have ht2p : 0 < t ^ 2 := by positivity
    exact ⟨mem_rtri hD7 TGT_pos (by unfold ef; linarith) (by unfold ef; linarith) (by unfold ef; linarith), not_mem_rtri_of_edge1 hD7 T0_pos (by unfold ef; linarith), not_mem_rtri_of_edge0 hD7 T1_pos (by unfold ef; linarith), not_mem_rtri_of_edge1 hD7 T2_pos (by unfold ef; linarith), not_mem_rtri_of_edge0 hD7 T3_pos (by unfold ef; linarith)⟩
  have hblocked : ∃ δ : ℝ, 0 < δ ∧ ∀ t s : ℝ, 0 < t → t < δ → 0 < s → s < δ →
      rp 7 8 0 + t • (rp 7 1 0 - s • perp (rp 7 1 0)) ∉ unfilled D.toDissection ([i0, i1, i2, i3] : List (Fin N)).toFinset := by
    exact hblocked_base hD7 D.toDissection _ (fun p hp => hyT p (htarget ▸ hp)) 8
  obtain ⟨j, hj, k₀, k₁, k₂, hk01, hk02, hk12, hk₀, ⟨c', hc', hk₁⟩, hk₂⟩ :=
    placement_completeness D.toDissection ([i0, i1, i2, i3] : List (Fin N)).toFinset (rp 7 8 0) (rp 7 1 0) (rp_unit hD7 (by norm_num)) hlex hfree hblocked
  have hcong : (D.tile j).Congruent MODEL := (D.tiles_congruent j).trans hmodel
  obtain ⟨hMa, hMb, hMc⟩ := MODEL_sides
  have hj0 : j ≠ i0 := fun h => hj (by rw [h]; simp)
  have hj1 : j ≠ i1 := fun h => hj (by rw [h]; simp)
  have hj2 : j ≠ i2 := fun h => hj (by rw [h]; simp)
  have hj3 : j ≠ i3 := fun h => hj (by rw [h]; simp)
  rcases six_placements hcong hMa hMb hMc (rp_unit hD7 (by norm_num)) hk01 hk02 hk12 hk₀ hc' hk₁ hk₂ with
    ⟨hP, hQ⟩ | ⟨hP, hQ⟩ | ⟨hP, hQ⟩ | ⟨hP, hQ⟩ | ⟨hP, hQ⟩ | ⟨hP, hQ⟩
  · -- placement 1: (4, 16, 15)
    have hP' : (D.tile j).pts k₁ = rp 7 12 0 := by rw [hP, rp_add_smul]; norm_num
    have hQ' : (D.tile j).pts k₂ = rp 7 (111/8) (45/8) := by
      rw [hQ, placeThird_rp hD7 8 0 1 0 4 16 15 (47/8) (45/8) (by norm_num) (by norm_num) (by norm_num)]; norm_num
    exact (escape_of D.toDissection htarget j k₂ hQ' (not_mem_rtri_of_edge1 hD7 TGT_pos (by unfold ef; norm_num)))
  · -- placement 2: (16, 4, 15)
    have hP' : (D.tile j).pts k₁ = rp 7 24 0 := by rw [hP, rp_add_smul]; norm_num
    have hQ' : (D.tile j).pts k₂ = rp 7 (303/32) (45/32) := by
      rw [hQ, placeThird_rp hD7 8 0 1 0 16 4 15 (47/32) (45/32) (by norm_num) (by norm_num) (by norm_num)]; norm_num
    exact (escape_of D.toDissection htarget j k₁ hP' (not_mem_rtri_of_edge1 hD7 TGT_pos (by unfold ef; norm_num)))
  · -- placement 3: (4, 15, 16)
    have hP' : (D.tile j).pts k₁ = rp 7 12 0 := by rw [hP, rp_add_smul]; norm_num
    have hQ' : (D.tile j).pts k₂ = rp 7 (49/8) (45/8) := by
      rw [hQ, placeThird_rp hD7 8 0 1 0 4 15 16 (-15/8) (45/8) (by norm_num) (by norm_num) (by norm_num)]; norm_num
    have hjc : (D.tile j).carrier = T4.carrier :=
      carrier_eq_rtri_of_pts hD7 _ hk01 hk02 hk12 hk₀ hP' hQ' T4_pos
    exact (overlap_of D.toDissection hj2.symm h2 hjc (w := rp 7 8 (3510/1457))
      (mem_interior_rtri hD7 T2_pos (by unfold ef; norm_num) (by unfold ef; norm_num) (by unfold ef; norm_num))
      (mem_interior_rtri hD7 T4_pos (by unfold ef; norm_num) (by unfold ef; norm_num) (by unfold ef; norm_num)))
  · -- placement 4: (15, 4, 16)
    have hP' : (D.tile j).pts k₁ = rp 7 23 0 := by rw [hP, rp_add_smul]; norm_num
    have hQ' : (D.tile j).pts k₂ = rp 7 (15/2) (3/2) := by
      rw [hQ, placeThird_rp hD7 8 0 1 0 15 4 16 (-1/2) (3/2) (by norm_num) (by norm_num) (by norm_num)]; norm_num
    exact (escape_of D.toDissection htarget j k₁ hP' (not_mem_rtri_of_edge1 hD7 TGT_pos (by unfold ef; norm_num)))
  · -- placement 5: (16, 15, 4)
    have hP' : (D.tile j).pts k₁ = rp 7 24 0 := by rw [hP, rp_add_smul]; norm_num
    have hQ' : (D.tile j).pts k₂ = rp 7 (721/32) (45/32) := by
      rw [hQ, placeThird_rp hD7 8 0 1 0 16 15 4 (465/32) (45/32) (by norm_num) (by norm_num) (by norm_num)]; norm_num
    exact (escape_of D.toDissection htarget j k₂ hQ' (not_mem_rtri_of_edge1 hD7 TGT_pos (by unfold ef; norm_num)))
  · -- placement 6: (15, 16, 4)
    have hP' : (D.tile j).pts k₁ = rp 7 23 0 := by rw [hP, rp_add_smul]; norm_num
    have hQ' : (D.tile j).pts k₂ = rp 7 (47/2) (3/2) := by
      rw [hQ, placeThird_rp hD7 8 0 1 0 15 16 4 (31/2) (3/2) (by norm_num) (by norm_num) (by norm_num)]; norm_num
    exact (escape_of D.toDissection htarget j k₂ hQ' (not_mem_rtri_of_edge1 hD7 TGT_pos (by unfold ef; norm_num)))

/-- Node 5: 4 placed tile(s), `v = (8, 0)`, `d = (1, 0)`; kills: escape(Q, edge 1), escape(P, edge 1), overlap(tile 2), escape(P, edge 1), escape(Q, edge 1), escape(Q, edge 1). -/
theorem node_5 {N : ℕ} (D : CongruentDissection N)
    (htarget : D.target.carrier = TGT.carrier) (hmodel : D.model.Congruent MODEL)
    (i0 i1 i2 i3 : Fin N) (h0 : (D.tile i0).carrier = T0.carrier) (h1 : (D.tile i1).carrier = T1.carrier) (h2 : (D.tile i2).carrier = T2.carrier) (h3 : (D.tile i3).carrier = T5.carrier)
    : False := by
  classical
  have hyT : ∀ p ∈ TGT.carrier, 0 ≤ p 1 := fun p hp => target_y_nonneg hD7 (by norm_num) TGT_pos hp
  have hU : ∀ p, p ∈ unfilled D.toDissection ([i0, i1, i2, i3] : List (Fin N)).toFinset ↔ p ∈ TGT.carrier ∧ p ∉ T0.carrier ∧ p ∉ T1.carrier ∧ p ∉ T2.carrier ∧ p ∉ T5.carrier := by
    intro p; rw [mem_unfilled_iff, htarget]
    simp [h0, h1, h2, h3]
  have hlex : ∀ p ∈ closure (unfilled D.toDissection ([i0, i1, i2, i3] : List (Fin N)).toFinset), LexLE (rp 7 8 0) p := by
    refine hlex_of D.toDissection _ _ ((TGT.carrier ∩ halfR 7 0 1 0) ∩ (halfR 7 1 0 (-8) ∪ ((halfR 7 (-45/8) (15/8) (45/2) ∩ (halfR 7 (-45/8) (47/8) 0 ∩ (halfR 7 0 4 (-45/2)))) ∪ ((halfR 7 (45/8) (-15/8) (-45/2) ∩ (halfR 7 (45/8) (-47/8) 0 ∩ (halfR 7 (-45/8) (47/8) 0))) ∪ ((halfR 7 (45/8) (-15/8) (-45/2) ∩ (halfR 7 (45/8) (-47/8) 0 ∩ (halfR 7 (45/8) (-47/8) 0 ∩ (halfR 7 0 (-4) (45/2) ∩ (halfR 7 (-45/8) (47/8) (45/2) ∩ (halfR 7 (93/128) (449/128) (-813/32))))))) ∪ ((halfR 7 (45/8) (-15/8) (-45/2) ∩ (halfR 7 (45/8) (-47/8) 0 ∩ (halfR 7 (45/8) (-47/8) 0 ∩ (halfR 7 0 4 (-45/2))))) ∪ ((halfR 7 (45/8) (-15/8) (-45/2) ∩ (halfR 7 (-45/8) (47/8) 0))))))))) ((TGT.isCompact.isClosed.inter (isClosed_halfR _ _ _ _)).inter ((isClosed_halfR _ _ _ _).union (((isClosed_halfR _ _ _ _).inter ((isClosed_halfR _ _ _ _).inter (isClosed_halfR _ _ _ _))).union (((isClosed_halfR _ _ _ _).inter ((isClosed_halfR _ _ _ _).inter (isClosed_halfR _ _ _ _))).union (((isClosed_halfR _ _ _ _).inter ((isClosed_halfR _ _ _ _).inter ((isClosed_halfR _ _ _ _).inter ((isClosed_halfR _ _ _ _).inter ((isClosed_halfR _ _ _ _).inter (isClosed_halfR _ _ _ _)))))).union (((isClosed_halfR _ _ _ _).inter ((isClosed_halfR _ _ _ _).inter ((isClosed_halfR _ _ _ _).inter (isClosed_halfR _ _ _ _)))).union ((isClosed_halfR _ _ _ _).inter (isClosed_halfR _ _ _ _)))))))) ?_ ?_
    · intro p hpT hnot
      obtain ⟨X, Y, rfl⟩ := exists_rp hD7 p
      have hpT' : rp 7 X Y ∈ TGT.carrier := htarget ▸ hpT
      obtain ⟨hT0, hT1, hT2⟩ := rtri_ef_nonneg hD7 TGT_pos hpT'
      unfold ef at hT0 hT1 hT2
      have hn0 : ¬ (0 ≤ 0 * X + 4 * Y + 0 ∧ 0 ≤ (-45/8) * X + (15/8) * Y + (45/2) ∧ 0 ≤ (45/8) * X + (-47/8) * Y + 0) := fun h =>
        hnot i0 (by simp) (by rw [h0]; exact mem_rtri hD7 T0_pos (by unfold ef; linarith [h.1]) (by unfold ef; linarith [h.2.1]) (by unfold ef; linarith [h.2.2]))
      have hn1 : ¬ (0 ≤ (-45/8) * X + (47/8) * Y + 0 ∧ 0 ≤ 0 * X + (-4) * Y + (45/2) ∧ 0 ≤ (45/8) * X + (-15/8) * Y + 0) := fun h =>
        hnot i1 (by simp) (by rw [h1]; exact mem_rtri hD7 T1_pos (by unfold ef; linarith [h.1]) (by unfold ef; linarith [h.2.1]) (by unfold ef; linarith [h.2.2]))
      have hn2 : ¬ (0 ≤ 0 * X + 4 * Y + 0 ∧ 0 ≤ (-45/8) * X + (15/8) * Y + 45 ∧ 0 ≤ (45/8) * X + (-47/8) * Y + (-45/2)) := fun h =>
        hnot i2 (by simp) (by rw [h2]; exact mem_rtri hD7 T2_pos (by unfold ef; linarith [h.1]) (by unfold ef; linarith [h.2.1]) (by unfold ef; linarith [h.2.2]))
      have hn3 : ¬ (0 ≤ (-675/128) * X + (705/128) * Y + (675/32) ∧ 0 ≤ (-93/128) * X + (-449/128) * Y + (813/32) ∧ 0 ≤ 6 * X + (-2) * Y + (-24)) := fun h =>
        hnot i3 (by simp) (by rw [h3]; exact mem_rtri hD7 T5_pos (by unfold ef; linarith [h.1]) (by unfold ef; linarith [h.2.1]) (by unfold ef; linarith [h.2.2]))
      have hY : 0 ≤ Y := by
        by_contra hR; push_neg at hR
        linarith
      simp only [Set.mem_inter_iff, Set.mem_union, mem_halfR_rp hD7]
      refine ⟨⟨hpT', by linarith⟩, ?_⟩
      rcases le_or_gt 8 X with hX | hX
      · exact Or.inl (by linarith)
      · -- the region X < xv, Y ≥ yv
        rcases le_or_gt 0 ((-45/8) * X + (15/8) * Y + (45/2)) with hg | hg
        · -- 0 ≤ (-45/8) * X + (15/8) * Y + (45/2)
          rcases le_or_gt 0 ((45/8) * X + (-47/8) * Y + 0) with hg | hg
          · -- 0 ≤ (45/8) * X + (-47/8) * Y + 0
            exact (hn0 ⟨by linarith, by linarith, by linarith⟩).elim
          · -- (45/8) * X + (-47/8) * Y + 0 < 0
            rcases le_or_gt 0 (0 * X + (-4) * Y + (45/2)) with hg | hg
            · -- 0 ≤ 0 * X + (-4) * Y + (45/2)
              exact (hn1 ⟨by linarith, by linarith, by linarith⟩).elim
            · -- 0 * X + (-4) * Y + (45/2) < 0
              exact Or.inr (Or.inl ⟨by linarith, by linarith, by linarith⟩)
        · -- (-45/8) * X + (15/8) * Y + (45/2) < 0
          rcases le_or_gt 0 ((45/8) * X + (-47/8) * Y + 0) with hg | hg
          · -- 0 ≤ (45/8) * X + (-47/8) * Y + 0
            rcases le_or_gt 0 ((-45/8) * X + (47/8) * Y + 0) with hg | hg
            · -- 0 ≤ (-45/8) * X + (47/8) * Y + 0
              exact Or.inr (Or.inr (Or.inl ⟨by linarith, by linarith, by linarith⟩))
            · -- (-45/8) * X + (47/8) * Y + 0 < 0
              rcases le_or_gt 0 (0 * X + (-4) * Y + (45/2)) with hg | hg
              · -- 0 ≤ 0 * X + (-4) * Y + (45/2)
                rcases le_or_gt 0 ((45/8) * X + (-47/8) * Y + (-45/2)) with hg | hg
                · -- 0 ≤ (45/8) * X + (-47/8) * Y + (-45/2)
                  exact (hn2 ⟨by linarith, by linarith, by linarith⟩).elim
                · -- (45/8) * X + (-47/8) * Y + (-45/2) < 0
                  rcases le_or_gt 0 ((-93/128) * X + (-449/128) * Y + (813/32)) with hg | hg
                  · -- 0 ≤ (-93/128) * X + (-449/128) * Y + (813/32)
                    exact (hn3 ⟨by linarith, by linarith, by linarith⟩).elim
                  · -- (-93/128) * X + (-449/128) * Y + (813/32) < 0
                    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩)))
              · -- 0 * X + (-4) * Y + (45/2) < 0
                exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by linarith, by linarith, by linarith, by linarith⟩))))
          · -- (45/8) * X + (-47/8) * Y + 0 < 0
            exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨by linarith, by linarith⟩)))))
    · intro p hp
      obtain ⟨X, Y, rfl⟩ := exists_rp hD7 p
      simp only [Set.mem_inter_iff, Set.mem_union, mem_halfR_rp hD7] at hp
      obtain ⟨⟨hpT, hY⟩, hdis⟩ := hp
      obtain ⟨hT0, hT1, hT2⟩ := rtri_ef_nonneg hD7 TGT_pos hpT
      unfold ef at hT0 hT1 hT2
      refine lexLE_rp hD7 (by linarith) (fun hYe => ?_)
      rcases hdis with h | ⟨c0, c1, c2⟩ | ⟨c0, c1, c2⟩ | ⟨c0, c1, c2, c3, c4, c5⟩ | ⟨c0, c1, c2, c3⟩ | ⟨c0, c1⟩ <;> linarith
  have hfree : ∀ ε : ℝ, 0 < ε → ∃ t s : ℝ, 0 < t ∧ t < ε ∧ 0 < s ∧ s < ε ∧
      rp 7 8 0 + t • (rp 7 1 0 + s • perp (rp 7 1 0)) ∈ unfilled D.toDissection ([i0, i1, i2, i3] : List (Fin N)).toFinset := by
    refine hfree_of hD7 (B := 3) (by norm_num) sr7_lt (τ := (1/4)) (by norm_num) _ _ _ ?_
    intro t ht htτ
    rw [pt_ccw_rp 7 hD7, hU]
    have ht2 : t ^ 2 ≤ (1/4) * t := by nlinarith [mul_le_mul_of_nonneg_left htτ ht.le]
    have ht2p : 0 < t ^ 2 := by positivity
    exact ⟨mem_rtri hD7 TGT_pos (by unfold ef; linarith) (by unfold ef; linarith) (by unfold ef; linarith), not_mem_rtri_of_edge1 hD7 T0_pos (by unfold ef; linarith), not_mem_rtri_of_edge0 hD7 T1_pos (by unfold ef; linarith), not_mem_rtri_of_edge1 hD7 T2_pos (by unfold ef; linarith), not_mem_rtri_of_edge0 hD7 T5_pos (by unfold ef; linarith)⟩
  have hblocked : ∃ δ : ℝ, 0 < δ ∧ ∀ t s : ℝ, 0 < t → t < δ → 0 < s → s < δ →
      rp 7 8 0 + t • (rp 7 1 0 - s • perp (rp 7 1 0)) ∉ unfilled D.toDissection ([i0, i1, i2, i3] : List (Fin N)).toFinset := by
    exact hblocked_base hD7 D.toDissection _ (fun p hp => hyT p (htarget ▸ hp)) 8
  obtain ⟨j, hj, k₀, k₁, k₂, hk01, hk02, hk12, hk₀, ⟨c', hc', hk₁⟩, hk₂⟩ :=
    placement_completeness D.toDissection ([i0, i1, i2, i3] : List (Fin N)).toFinset (rp 7 8 0) (rp 7 1 0) (rp_unit hD7 (by norm_num)) hlex hfree hblocked
  have hcong : (D.tile j).Congruent MODEL := (D.tiles_congruent j).trans hmodel
  obtain ⟨hMa, hMb, hMc⟩ := MODEL_sides
  have hj0 : j ≠ i0 := fun h => hj (by rw [h]; simp)
  have hj1 : j ≠ i1 := fun h => hj (by rw [h]; simp)
  have hj2 : j ≠ i2 := fun h => hj (by rw [h]; simp)
  have hj3 : j ≠ i3 := fun h => hj (by rw [h]; simp)
  rcases six_placements hcong hMa hMb hMc (rp_unit hD7 (by norm_num)) hk01 hk02 hk12 hk₀ hc' hk₁ hk₂ with
    ⟨hP, hQ⟩ | ⟨hP, hQ⟩ | ⟨hP, hQ⟩ | ⟨hP, hQ⟩ | ⟨hP, hQ⟩ | ⟨hP, hQ⟩
  · -- placement 1: (4, 16, 15)
    have hP' : (D.tile j).pts k₁ = rp 7 12 0 := by rw [hP, rp_add_smul]; norm_num
    have hQ' : (D.tile j).pts k₂ = rp 7 (111/8) (45/8) := by
      rw [hQ, placeThird_rp hD7 8 0 1 0 4 16 15 (47/8) (45/8) (by norm_num) (by norm_num) (by norm_num)]; norm_num
    exact (escape_of D.toDissection htarget j k₂ hQ' (not_mem_rtri_of_edge1 hD7 TGT_pos (by unfold ef; norm_num)))
  · -- placement 2: (16, 4, 15)
    have hP' : (D.tile j).pts k₁ = rp 7 24 0 := by rw [hP, rp_add_smul]; norm_num
    have hQ' : (D.tile j).pts k₂ = rp 7 (303/32) (45/32) := by
      rw [hQ, placeThird_rp hD7 8 0 1 0 16 4 15 (47/32) (45/32) (by norm_num) (by norm_num) (by norm_num)]; norm_num
    exact (escape_of D.toDissection htarget j k₁ hP' (not_mem_rtri_of_edge1 hD7 TGT_pos (by unfold ef; norm_num)))
  · -- placement 3: (4, 15, 16)
    have hP' : (D.tile j).pts k₁ = rp 7 12 0 := by rw [hP, rp_add_smul]; norm_num
    have hQ' : (D.tile j).pts k₂ = rp 7 (49/8) (45/8) := by
      rw [hQ, placeThird_rp hD7 8 0 1 0 4 15 16 (-15/8) (45/8) (by norm_num) (by norm_num) (by norm_num)]; norm_num
    have hjc : (D.tile j).carrier = T4.carrier :=
      carrier_eq_rtri_of_pts hD7 _ hk01 hk02 hk12 hk₀ hP' hQ' T4_pos
    exact (overlap_of D.toDissection hj2.symm h2 hjc (w := rp 7 8 (3510/1457))
      (mem_interior_rtri hD7 T2_pos (by unfold ef; norm_num) (by unfold ef; norm_num) (by unfold ef; norm_num))
      (mem_interior_rtri hD7 T4_pos (by unfold ef; norm_num) (by unfold ef; norm_num) (by unfold ef; norm_num)))
  · -- placement 4: (15, 4, 16)
    have hP' : (D.tile j).pts k₁ = rp 7 23 0 := by rw [hP, rp_add_smul]; norm_num
    have hQ' : (D.tile j).pts k₂ = rp 7 (15/2) (3/2) := by
      rw [hQ, placeThird_rp hD7 8 0 1 0 15 4 16 (-1/2) (3/2) (by norm_num) (by norm_num) (by norm_num)]; norm_num
    exact (escape_of D.toDissection htarget j k₁ hP' (not_mem_rtri_of_edge1 hD7 TGT_pos (by unfold ef; norm_num)))
  · -- placement 5: (16, 15, 4)
    have hP' : (D.tile j).pts k₁ = rp 7 24 0 := by rw [hP, rp_add_smul]; norm_num
    have hQ' : (D.tile j).pts k₂ = rp 7 (721/32) (45/32) := by
      rw [hQ, placeThird_rp hD7 8 0 1 0 16 15 4 (465/32) (45/32) (by norm_num) (by norm_num) (by norm_num)]; norm_num
    exact (escape_of D.toDissection htarget j k₂ hQ' (not_mem_rtri_of_edge1 hD7 TGT_pos (by unfold ef; norm_num)))
  · -- placement 6: (15, 16, 4)
    have hP' : (D.tile j).pts k₁ = rp 7 23 0 := by rw [hP, rp_add_smul]; norm_num
    have hQ' : (D.tile j).pts k₂ = rp 7 (47/2) (3/2) := by
      rw [hQ, placeThird_rp hD7 8 0 1 0 15 16 4 (31/2) (3/2) (by norm_num) (by norm_num) (by norm_num)]; norm_num
    exact (escape_of D.toDissection htarget j k₂ hQ' (not_mem_rtri_of_edge1 hD7 TGT_pos (by unfold ef; norm_num)))

/-- Node 3: 3 placed tile(s), `v = (4, 0)`, `d = (47/128, 45/128·r)`; kills: escape(Q, edge 2), overlap(tile 0), escape(Q, edge 2), overlap(tile 0), child 4, child 5. -/
theorem node_3 {N : ℕ} (D : CongruentDissection N)
    (htarget : D.target.carrier = TGT.carrier) (hmodel : D.model.Congruent MODEL)
    (i0 i1 i2 : Fin N) (h0 : (D.tile i0).carrier = T0.carrier) (h1 : (D.tile i1).carrier = T1.carrier) (h2 : (D.tile i2).carrier = T2.carrier)
    : False := by
  classical
  have hyT : ∀ p ∈ TGT.carrier, 0 ≤ p 1 := fun p hp => target_y_nonneg hD7 (by norm_num) TGT_pos hp
  have hU : ∀ p, p ∈ unfilled D.toDissection ([i0, i1, i2] : List (Fin N)).toFinset ↔ p ∈ TGT.carrier ∧ p ∉ T0.carrier ∧ p ∉ T1.carrier ∧ p ∉ T2.carrier := by
    intro p; rw [mem_unfilled_iff, htarget]
    simp [h0, h1, h2]
  have hlex : ∀ p ∈ closure (unfilled D.toDissection ([i0, i1, i2] : List (Fin N)).toFinset), LexLE (rp 7 4 0) p := by
    refine hlex_of D.toDissection _ _ ((TGT.carrier ∩ halfR 7 0 1 0) ∩ (halfR 7 1 0 (-4) ∪ ((halfR 7 (-45/8) (47/8) 0 ∩ (halfR 7 0 4 (-45/2)))))) ((TGT.isCompact.isClosed.inter (isClosed_halfR _ _ _ _)).inter ((isClosed_halfR _ _ _ _).union ((isClosed_halfR _ _ _ _).inter (isClosed_halfR _ _ _ _)))) ?_ ?_
    · intro p hpT hnot
      obtain ⟨X, Y, rfl⟩ := exists_rp hD7 p
      have hpT' : rp 7 X Y ∈ TGT.carrier := htarget ▸ hpT
      obtain ⟨hT0, hT1, hT2⟩ := rtri_ef_nonneg hD7 TGT_pos hpT'
      unfold ef at hT0 hT1 hT2
      have hn0 : ¬ (0 ≤ 0 * X + 4 * Y + 0 ∧ 0 ≤ (-45/8) * X + (15/8) * Y + (45/2) ∧ 0 ≤ (45/8) * X + (-47/8) * Y + 0) := fun h =>
        hnot i0 (by simp) (by rw [h0]; exact mem_rtri hD7 T0_pos (by unfold ef; linarith [h.1]) (by unfold ef; linarith [h.2.1]) (by unfold ef; linarith [h.2.2]))
      have hn1 : ¬ (0 ≤ (-45/8) * X + (47/8) * Y + 0 ∧ 0 ≤ 0 * X + (-4) * Y + (45/2) ∧ 0 ≤ (45/8) * X + (-15/8) * Y + 0) := fun h =>
        hnot i1 (by simp) (by rw [h1]; exact mem_rtri hD7 T1_pos (by unfold ef; linarith [h.1]) (by unfold ef; linarith [h.2.1]) (by unfold ef; linarith [h.2.2]))
      have hn2 : ¬ (0 ≤ 0 * X + 4 * Y + 0 ∧ 0 ≤ (-45/8) * X + (15/8) * Y + 45 ∧ 0 ≤ (45/8) * X + (-47/8) * Y + (-45/2)) := fun h =>
        hnot i2 (by simp) (by rw [h2]; exact mem_rtri hD7 T2_pos (by unfold ef; linarith [h.1]) (by unfold ef; linarith [h.2.1]) (by unfold ef; linarith [h.2.2]))
      have hY : 0 ≤ Y := by
        by_contra hR; push_neg at hR
        linarith
      simp only [Set.mem_inter_iff, Set.mem_union, mem_halfR_rp hD7]
      refine ⟨⟨hpT', by linarith⟩, ?_⟩
      rcases le_or_gt 4 X with hX | hX
      · exact Or.inl (by linarith)
      · -- the region X < xv, Y ≥ yv
        rcases le_or_gt 0 ((45/8) * X + (-47/8) * Y + 0) with hg | hg
        · -- 0 ≤ (45/8) * X + (-47/8) * Y + 0
          exact (hn0 ⟨by linarith, by linarith, by linarith⟩).elim
        · -- (45/8) * X + (-47/8) * Y + 0 < 0
          rcases le_or_gt 0 (0 * X + (-4) * Y + (45/2)) with hg | hg
          · -- 0 ≤ 0 * X + (-4) * Y + (45/2)
            exact (hn1 ⟨by linarith, by linarith, by linarith⟩).elim
          · -- 0 * X + (-4) * Y + (45/2) < 0
            exact Or.inr (⟨by linarith, by linarith⟩)
    · intro p hp
      obtain ⟨X, Y, rfl⟩ := exists_rp hD7 p
      simp only [Set.mem_inter_iff, Set.mem_union, mem_halfR_rp hD7] at hp
      obtain ⟨⟨hpT, hY⟩, hdis⟩ := hp
      obtain ⟨hT0, hT1, hT2⟩ := rtri_ef_nonneg hD7 TGT_pos hpT
      unfold ef at hT0 hT1 hT2
      refine lexLE_rp hD7 (by linarith) (fun hYe => ?_)
      rcases hdis with h | ⟨c0, c1⟩ <;> linarith
  have hfree : ∀ ε : ℝ, 0 < ε → ∃ t s : ℝ, 0 < t ∧ t < ε ∧ 0 < s ∧ s < ε ∧
      rp 7 4 0 + t • (rp 7 (47/128) (45/128) + s • perp (rp 7 (47/128) (45/128))) ∈ unfilled D.toDissection ([i0, i1, i2] : List (Fin N)).toFinset := by
    refine hfree_of hD7 (B := 3) (by norm_num) sr7_lt (τ := (1/16)) (by norm_num) _ _ _ ?_
    intro t ht htτ
    rw [pt_ccw_rp 7 hD7, hU]
    have ht2 : t ^ 2 ≤ (1/16) * t := by nlinarith [mul_le_mul_of_nonneg_left htτ ht.le]
    have ht2p : 0 < t ^ 2 := by positivity
    exact ⟨mem_rtri hD7 TGT_pos (by unfold ef; linarith) (by unfold ef; linarith) (by unfold ef; linarith), not_mem_rtri_of_edge1 hD7 T0_pos (by unfold ef; linarith), not_mem_rtri_of_edge0 hD7 T1_pos (by unfold ef; linarith), not_mem_rtri_of_edge2 hD7 T2_pos (by unfold ef; linarith)⟩
  have hblocked : ∃ δ : ℝ, 0 < δ ∧ ∀ t s : ℝ, 0 < t → t < δ → 0 < s → s < δ →
      rp 7 4 0 + t • (rp 7 (47/128) (45/128) - s • perp (rp 7 (47/128) (45/128))) ∉ unfilled D.toDissection ([i0, i1, i2] : List (Fin N)).toFinset := by
    have hsub : T2.carrier ⊆ (D.tile i2).carrier := (h2.trans
      (carrier_eq_rtri_of_pts hD7 T2 (k₀ := 0) (k₁ := 1) (k₂ := 2) (by decide) (by decide) (by decide) rfl rfl rfl T2_pos)).symm.subset
    refine hblocked_of_wedge hD7 sr7_gt1 D.toDissection _ (i := i2) (by simp) _ _ T2 hsub rfl
      (wedge_interior T2 (rp 7 (47/128) (45/128)) (sr 7 • perp (rp 7 (47/128) (45/128))) 0 (1/16) (-32/45) (47/720) ?_ ?_ ?_ ?_)
    · rw [T2_pts.1, T2_pts.2.1, T2_pts.2.2]; refine plane_ext ?_ ?_ <;> simp <;> ring
    · rw [sr_smul_perp_rp hD7, T2_pts.1, T2_pts.2.1, T2_pts.2.2]; refine plane_ext ?_ ?_ <;> simp <;> ring
    · exact Or.inr ⟨by norm_num, by norm_num⟩
    · exact Or.inl (by norm_num)
  obtain ⟨j, hj, k₀, k₁, k₂, hk01, hk02, hk12, hk₀, ⟨c', hc', hk₁⟩, hk₂⟩ :=
    placement_completeness D.toDissection ([i0, i1, i2] : List (Fin N)).toFinset (rp 7 4 0) (rp 7 (47/128) (45/128)) (rp_unit hD7 (by norm_num)) hlex hfree hblocked
  have hcong : (D.tile j).Congruent MODEL := (D.tiles_congruent j).trans hmodel
  obtain ⟨hMa, hMb, hMc⟩ := MODEL_sides
  have hj0 : j ≠ i0 := fun h => hj (by rw [h]; simp)
  have hj1 : j ≠ i1 := fun h => hj (by rw [h]; simp)
  have hj2 : j ≠ i2 := fun h => hj (by rw [h]; simp)
  rcases six_placements hcong hMa hMb hMc (rp_unit hD7 (by norm_num)) hk01 hk02 hk12 hk₀ hc' hk₁ hk₂ with
    ⟨hP, hQ⟩ | ⟨hP, hQ⟩ | ⟨hP, hQ⟩ | ⟨hP, hQ⟩ | ⟨hP, hQ⟩ | ⟨hP, hQ⟩
  · -- placement 1: (4, 16, 15)
    have hP' : (D.tile j).pts k₁ = rp 7 (175/32) (45/32) := by rw [hP, rp_add_smul]; norm_num
    have hQ' : (D.tile j).pts k₂ = rp 7 (-3935/512) (2115/512) := by
      rw [hQ, placeThird_rp hD7 4 0 (47/128) (45/128) 4 16 15 (47/8) (45/8) (by norm_num) (by norm_num) (by norm_num)]; norm_num
    exact (escape_of D.toDissection htarget j k₂ hQ' (not_mem_rtri_of_edge2 hD7 TGT_pos (by unfold ef; norm_num)))
  · -- placement 2: (16, 4, 15)
    have hP' : (D.tile j).pts k₁ = rp 7 (79/8) (45/8) := by rw [hP, rp_add_smul]; norm_num
    have hQ' : (D.tile j).pts k₂ = rp 7 (2209/2048) (2115/2048) := by
      rw [hQ, placeThird_rp hD7 4 0 (47/128) (45/128) 16 4 15 (47/32) (45/32) (by norm_num) (by norm_num) (by norm_num)]; norm_num
    have hjc : (D.tile j).carrier = T6.carrier :=
      carrier_eq_rtri_of_pts hD7 _ hk01 hk02 hk12 hk₀ hP' hQ' T6_pos
    exact (overlap_of D.toDissection hj0.symm h0 hjc (w := rp 7 (213973/63488) (87391/63488))
      (mem_interior_rtri hD7 T0_pos (by unfold ef; norm_num) (by unfold ef; norm_num) (by unfold ef; norm_num))
      (mem_interior_rtri hD7 T6_pos (by unfold ef; norm_num) (by unfold ef; norm_num) (by unfold ef; norm_num)))
  · -- placement 3: (4, 15, 16)
    have hP' : (D.tile j).pts k₁ = rp 7 (175/32) (45/32) := by rw [hP, rp_add_smul]; norm_num
    have hQ' : (D.tile j).pts k₂ = rp 7 (-337/32) (45/32) := by
      rw [hQ, placeThird_rp hD7 4 0 (47/128) (45/128) 4 15 16 (-15/8) (45/8) (by norm_num) (by norm_num) (by norm_num)]; norm_num
    exact (escape_of D.toDissection htarget j k₂ hQ' (not_mem_rtri_of_edge2 hD7 TGT_pos (by unfold ef; norm_num)))
  · -- placement 4: (15, 4, 16)
    have hP' : (D.tile j).pts k₁ = rp 7 (1217/128) (675/128) := by rw [hP, rp_add_smul]; norm_num
    have hQ' : (D.tile j).pts k₂ = rp 7 (1/8) (3/8) := by
      rw [hQ, placeThird_rp hD7 4 0 (47/128) (45/128) 15 4 16 (-1/2) (3/2) (by norm_num) (by norm_num) (by norm_num)]; norm_num
    have hjc : (D.tile j).carrier = T7.carrier :=
      carrier_eq_rtri_of_pts hD7 _ hk01 hk02 hk12 hk₀ hP' hQ' T7_pos
    exact (overlap_of D.toDissection hj0.symm h0 hjc (w := rp 7 (637823/253952) (249885/253952))
      (mem_interior_rtri hD7 T0_pos (by unfold ef; norm_num) (by unfold ef; norm_num) (by unfold ef; norm_num))
      (mem_interior_rtri hD7 T7_pos (by unfold ef; norm_num) (by unfold ef; norm_num) (by unfold ef; norm_num)))
  · -- placement 5: (16, 15, 4)
    have hP' : (D.tile j).pts k₁ = rp 7 (79/8) (45/8) := by rw [hP, rp_add_smul]; norm_num
    have hQ' : (D.tile j).pts k₂ = rp 7 (47/8) (45/8) := by
      rw [hQ, placeThird_rp hD7 4 0 (47/128) (45/128) 16 15 4 (465/32) (45/32) (by norm_num) (by norm_num) (by norm_num)]; norm_num
    have hjc : (D.tile j).carrier = T3.carrier :=
      carrier_eq_rtri_of_pts hD7 _ hk01 hk02 hk12 hk₀ hP' hQ' T3_pos
    exact node_4 D htarget hmodel i0 i1 i2 j h0 h1 h2 hjc
  · -- placement 6: (15, 16, 4)
    have hP' : (D.tile j).pts k₁ = rp 7 (1217/128) (675/128) := by rw [hP, rp_add_smul]; norm_num
    have hQ' : (D.tile j).pts k₂ = rp 7 6 6 := by
      rw [hQ, placeThird_rp hD7 4 0 (47/128) (45/128) 15 16 4 (31/2) (3/2) (by norm_num) (by norm_num) (by norm_num)]; norm_num
    have hjc : (D.tile j).carrier = T5.carrier :=
      carrier_eq_rtri_of_pts hD7 _ hk01 hk02 hk12 hk₀ hP' hQ' T5_pos
    exact node_5 D htarget hmodel i0 i1 i2 j h0 h1 h2 hjc

/-- Node 2: 2 placed tile(s), `v = (4, 0)`, `d = (1, 0)`; kills: child 3, escape(P, edge 1), overlap(tile 0), escape(P, edge 1), escape(Q, edge 1), escape(Q, edge 1). -/
theorem node_2 {N : ℕ} (D : CongruentDissection N)
    (htarget : D.target.carrier = TGT.carrier) (hmodel : D.model.Congruent MODEL)
    (i0 i1 : Fin N) (h0 : (D.tile i0).carrier = T0.carrier) (h1 : (D.tile i1).carrier = T1.carrier)
    : False := by
  classical
  have hyT : ∀ p ∈ TGT.carrier, 0 ≤ p 1 := fun p hp => target_y_nonneg hD7 (by norm_num) TGT_pos hp
  have hU : ∀ p, p ∈ unfilled D.toDissection ([i0, i1] : List (Fin N)).toFinset ↔ p ∈ TGT.carrier ∧ p ∉ T0.carrier ∧ p ∉ T1.carrier := by
    intro p; rw [mem_unfilled_iff, htarget]
    simp [h0, h1]
  have hlex : ∀ p ∈ closure (unfilled D.toDissection ([i0, i1] : List (Fin N)).toFinset), LexLE (rp 7 4 0) p := by
    refine hlex_of D.toDissection _ _ ((TGT.carrier ∩ halfR 7 0 1 0) ∩ (halfR 7 1 0 (-4) ∪ ((halfR 7 (-45/8) (47/8) 0 ∩ (halfR 7 0 4 (-45/2)))))) ((TGT.isCompact.isClosed.inter (isClosed_halfR _ _ _ _)).inter ((isClosed_halfR _ _ _ _).union ((isClosed_halfR _ _ _ _).inter (isClosed_halfR _ _ _ _)))) ?_ ?_
    · intro p hpT hnot
      obtain ⟨X, Y, rfl⟩ := exists_rp hD7 p
      have hpT' : rp 7 X Y ∈ TGT.carrier := htarget ▸ hpT
      obtain ⟨hT0, hT1, hT2⟩ := rtri_ef_nonneg hD7 TGT_pos hpT'
      unfold ef at hT0 hT1 hT2
      have hn0 : ¬ (0 ≤ 0 * X + 4 * Y + 0 ∧ 0 ≤ (-45/8) * X + (15/8) * Y + (45/2) ∧ 0 ≤ (45/8) * X + (-47/8) * Y + 0) := fun h =>
        hnot i0 (by simp) (by rw [h0]; exact mem_rtri hD7 T0_pos (by unfold ef; linarith [h.1]) (by unfold ef; linarith [h.2.1]) (by unfold ef; linarith [h.2.2]))
      have hn1 : ¬ (0 ≤ (-45/8) * X + (47/8) * Y + 0 ∧ 0 ≤ 0 * X + (-4) * Y + (45/2) ∧ 0 ≤ (45/8) * X + (-15/8) * Y + 0) := fun h =>
        hnot i1 (by simp) (by rw [h1]; exact mem_rtri hD7 T1_pos (by unfold ef; linarith [h.1]) (by unfold ef; linarith [h.2.1]) (by unfold ef; linarith [h.2.2]))
      have hY : 0 ≤ Y := by
        by_contra hR; push_neg at hR
        linarith
      simp only [Set.mem_inter_iff, Set.mem_union, mem_halfR_rp hD7]
      refine ⟨⟨hpT', by linarith⟩, ?_⟩
      rcases le_or_gt 4 X with hX | hX
      · exact Or.inl (by linarith)
      · -- the region X < xv, Y ≥ yv
        rcases le_or_gt 0 ((45/8) * X + (-47/8) * Y + 0) with hg | hg
        · -- 0 ≤ (45/8) * X + (-47/8) * Y + 0
          exact (hn0 ⟨by linarith, by linarith, by linarith⟩).elim
        · -- (45/8) * X + (-47/8) * Y + 0 < 0
          rcases le_or_gt 0 (0 * X + (-4) * Y + (45/2)) with hg | hg
          · -- 0 ≤ 0 * X + (-4) * Y + (45/2)
            exact (hn1 ⟨by linarith, by linarith, by linarith⟩).elim
          · -- 0 * X + (-4) * Y + (45/2) < 0
            exact Or.inr (⟨by linarith, by linarith⟩)
    · intro p hp
      obtain ⟨X, Y, rfl⟩ := exists_rp hD7 p
      simp only [Set.mem_inter_iff, Set.mem_union, mem_halfR_rp hD7] at hp
      obtain ⟨⟨hpT, hY⟩, hdis⟩ := hp
      obtain ⟨hT0, hT1, hT2⟩ := rtri_ef_nonneg hD7 TGT_pos hpT
      unfold ef at hT0 hT1 hT2
      refine lexLE_rp hD7 (by linarith) (fun hYe => ?_)
      rcases hdis with h | ⟨c0, c1⟩ <;> linarith
  have hfree : ∀ ε : ℝ, 0 < ε → ∃ t s : ℝ, 0 < t ∧ t < ε ∧ 0 < s ∧ s < ε ∧
      rp 7 4 0 + t • (rp 7 1 0 + s • perp (rp 7 1 0)) ∈ unfilled D.toDissection ([i0, i1] : List (Fin N)).toFinset := by
    refine hfree_of hD7 (B := 3) (by norm_num) sr7_lt (τ := (1/4)) (by norm_num) _ _ _ ?_
    intro t ht htτ
    rw [pt_ccw_rp 7 hD7, hU]
    have ht2 : t ^ 2 ≤ (1/4) * t := by nlinarith [mul_le_mul_of_nonneg_left htτ ht.le]
    have ht2p : 0 < t ^ 2 := by positivity
    exact ⟨mem_rtri hD7 TGT_pos (by unfold ef; linarith) (by unfold ef; linarith) (by unfold ef; linarith), not_mem_rtri_of_edge1 hD7 T0_pos (by unfold ef; linarith), not_mem_rtri_of_edge0 hD7 T1_pos (by unfold ef; linarith)⟩
  have hblocked : ∃ δ : ℝ, 0 < δ ∧ ∀ t s : ℝ, 0 < t → t < δ → 0 < s → s < δ →
      rp 7 4 0 + t • (rp 7 1 0 - s • perp (rp 7 1 0)) ∉ unfilled D.toDissection ([i0, i1] : List (Fin N)).toFinset := by
    exact hblocked_base hD7 D.toDissection _ (fun p hp => hyT p (htarget ▸ hp)) 4
  obtain ⟨j, hj, k₀, k₁, k₂, hk01, hk02, hk12, hk₀, ⟨c', hc', hk₁⟩, hk₂⟩ :=
    placement_completeness D.toDissection ([i0, i1] : List (Fin N)).toFinset (rp 7 4 0) (rp 7 1 0) (rp_unit hD7 (by norm_num)) hlex hfree hblocked
  have hcong : (D.tile j).Congruent MODEL := (D.tiles_congruent j).trans hmodel
  obtain ⟨hMa, hMb, hMc⟩ := MODEL_sides
  have hj0 : j ≠ i0 := fun h => hj (by rw [h]; simp)
  have hj1 : j ≠ i1 := fun h => hj (by rw [h]; simp)
  rcases six_placements hcong hMa hMb hMc (rp_unit hD7 (by norm_num)) hk01 hk02 hk12 hk₀ hc' hk₁ hk₂ with
    ⟨hP, hQ⟩ | ⟨hP, hQ⟩ | ⟨hP, hQ⟩ | ⟨hP, hQ⟩ | ⟨hP, hQ⟩ | ⟨hP, hQ⟩
  · -- placement 1: (4, 16, 15)
    have hP' : (D.tile j).pts k₁ = rp 7 8 0 := by rw [hP, rp_add_smul]; norm_num
    have hQ' : (D.tile j).pts k₂ = rp 7 (79/8) (45/8) := by
      rw [hQ, placeThird_rp hD7 4 0 1 0 4 16 15 (47/8) (45/8) (by norm_num) (by norm_num) (by norm_num)]; norm_num
    have hjc : (D.tile j).carrier = T2.carrier :=
      carrier_eq_rtri_of_pts hD7 _ hk01 hk02 hk12 hk₀ hP' hQ' T2_pos
    exact node_3 D htarget hmodel i0 i1 j h0 h1 hjc
  · -- placement 2: (16, 4, 15)
    have hP' : (D.tile j).pts k₁ = rp 7 20 0 := by rw [hP, rp_add_smul]; norm_num
    have hQ' : (D.tile j).pts k₂ = rp 7 (175/32) (45/32) := by
      rw [hQ, placeThird_rp hD7 4 0 1 0 16 4 15 (47/32) (45/32) (by norm_num) (by norm_num) (by norm_num)]; norm_num
    exact (escape_of D.toDissection htarget j k₁ hP' (not_mem_rtri_of_edge1 hD7 TGT_pos (by unfold ef; norm_num)))
  · -- placement 3: (4, 15, 16)
    have hP' : (D.tile j).pts k₁ = rp 7 8 0 := by rw [hP, rp_add_smul]; norm_num
    have hQ' : (D.tile j).pts k₂ = rp 7 (17/8) (45/8) := by
      rw [hQ, placeThird_rp hD7 4 0 1 0 4 15 16 (-15/8) (45/8) (by norm_num) (by norm_num) (by norm_num)]; norm_num
    have hjc : (D.tile j).carrier = T8.carrier :=
      carrier_eq_rtri_of_pts hD7 _ hk01 hk02 hk12 hk₀ hP' hQ' T8_pos
    exact (overlap_of D.toDissection hj0.symm h0 hjc (w := rp 7 4 (3510/1457))
      (mem_interior_rtri hD7 T0_pos (by unfold ef; norm_num) (by unfold ef; norm_num) (by unfold ef; norm_num))
      (mem_interior_rtri hD7 T8_pos (by unfold ef; norm_num) (by unfold ef; norm_num) (by unfold ef; norm_num)))
  · -- placement 4: (15, 4, 16)
    have hP' : (D.tile j).pts k₁ = rp 7 19 0 := by rw [hP, rp_add_smul]; norm_num
    have hQ' : (D.tile j).pts k₂ = rp 7 (7/2) (3/2) := by
      rw [hQ, placeThird_rp hD7 4 0 1 0 15 4 16 (-1/2) (3/2) (by norm_num) (by norm_num) (by norm_num)]; norm_num
    exact (escape_of D.toDissection htarget j k₁ hP' (not_mem_rtri_of_edge1 hD7 TGT_pos (by unfold ef; norm_num)))
  · -- placement 5: (16, 15, 4)
    have hP' : (D.tile j).pts k₁ = rp 7 20 0 := by rw [hP, rp_add_smul]; norm_num
    have hQ' : (D.tile j).pts k₂ = rp 7 (593/32) (45/32) := by
      rw [hQ, placeThird_rp hD7 4 0 1 0 16 15 4 (465/32) (45/32) (by norm_num) (by norm_num) (by norm_num)]; norm_num
    exact (escape_of D.toDissection htarget j k₂ hQ' (not_mem_rtri_of_edge1 hD7 TGT_pos (by unfold ef; norm_num)))
  · -- placement 6: (15, 16, 4)
    have hP' : (D.tile j).pts k₁ = rp 7 19 0 := by rw [hP, rp_add_smul]; norm_num
    have hQ' : (D.tile j).pts k₂ = rp 7 (39/2) (3/2) := by
      rw [hQ, placeThird_rp hD7 4 0 1 0 15 16 4 (31/2) (3/2) (by norm_num) (by norm_num) (by norm_num)]; norm_num
    exact (escape_of D.toDissection htarget j k₂ hQ' (not_mem_rtri_of_edge1 hD7 TGT_pos (by unfold ef; norm_num)))

/-- Node 8: 4 placed tile(s), `v = (8, 0)`, `d = (1, 0)`; kills: escape(Q, edge 1), escape(P, edge 1), overlap(tile 2), escape(P, edge 1), escape(Q, edge 1), escape(Q, edge 1). -/
theorem node_8 {N : ℕ} (D : CongruentDissection N)
    (htarget : D.target.carrier = TGT.carrier) (hmodel : D.model.Congruent MODEL)
    (i0 i1 i2 i3 : Fin N) (h0 : (D.tile i0).carrier = T0.carrier) (h1 : (D.tile i1).carrier = T9.carrier) (h2 : (D.tile i2).carrier = T2.carrier) (h3 : (D.tile i3).carrier = T3.carrier)
    : False := by
  classical
  have hyT : ∀ p ∈ TGT.carrier, 0 ≤ p 1 := fun p hp => target_y_nonneg hD7 (by norm_num) TGT_pos hp
  have hU : ∀ p, p ∈ unfilled D.toDissection ([i0, i1, i2, i3] : List (Fin N)).toFinset ↔ p ∈ TGT.carrier ∧ p ∉ T0.carrier ∧ p ∉ T9.carrier ∧ p ∉ T2.carrier ∧ p ∉ T3.carrier := by
    intro p; rw [mem_unfilled_iff, htarget]
    simp [h0, h1, h2, h3]
  have hlex : ∀ p ∈ closure (unfilled D.toDissection ([i0, i1, i2, i3] : List (Fin N)).toFinset), LexLE (rp 7 8 0) p := by
    refine hlex_of D.toDissection _ _ ((TGT.carrier ∩ halfR 7 0 1 0) ∩ (halfR 7 1 0 (-8) ∪ ((halfR 7 (-45/8) (15/8) (45/2) ∩ (halfR 7 (-45/8) (47/8) 0 ∩ (halfR 7 (93/128) (449/128) (-45/2)))) ∪ ((halfR 7 (45/8) (-15/8) (-45/2) ∩ (halfR 7 (45/8) (-47/8) 0 ∩ (halfR 7 (-675/128) (705/128) 0))) ∪ ((halfR 7 (45/8) (-15/8) (-45/2) ∩ (halfR 7 (45/8) (-47/8) 0 ∩ (halfR 7 (675/128) (-705/128) 0 ∩ (halfR 7 (93/128) (449/128) (-45/2))))) ∪ ((halfR 7 (45/8) (-15/8) (-45/2) ∩ (halfR 7 (-45/8) (47/8) 0)))))))) ((TGT.isCompact.isClosed.inter (isClosed_halfR _ _ _ _)).inter ((isClosed_halfR _ _ _ _).union (((isClosed_halfR _ _ _ _).inter ((isClosed_halfR _ _ _ _).inter (isClosed_halfR _ _ _ _))).union (((isClosed_halfR _ _ _ _).inter ((isClosed_halfR _ _ _ _).inter (isClosed_halfR _ _ _ _))).union (((isClosed_halfR _ _ _ _).inter ((isClosed_halfR _ _ _ _).inter ((isClosed_halfR _ _ _ _).inter (isClosed_halfR _ _ _ _)))).union ((isClosed_halfR _ _ _ _).inter (isClosed_halfR _ _ _ _))))))) ?_ ?_
    · intro p hpT hnot
      obtain ⟨X, Y, rfl⟩ := exists_rp hD7 p
      have hpT' : rp 7 X Y ∈ TGT.carrier := htarget ▸ hpT
      obtain ⟨hT0, hT1, hT2⟩ := rtri_ef_nonneg hD7 TGT_pos hpT'
      unfold ef at hT0 hT1 hT2
      have hn0 : ¬ (0 ≤ 0 * X + 4 * Y + 0 ∧ 0 ≤ (-45/8) * X + (15/8) * Y + (45/2) ∧ 0 ≤ (45/8) * X + (-47/8) * Y + 0) := fun h =>
        hnot i0 (by simp) (by rw [h0]; exact mem_rtri hD7 T0_pos (by unfold ef; linarith [h.1]) (by unfold ef; linarith [h.2.1]) (by unfold ef; linarith [h.2.2]))
      have hn1 : ¬ (0 ≤ (-675/128) * X + (705/128) * Y + 0 ∧ 0 ≤ (-93/128) * X + (-449/128) * Y + (45/2) ∧ 0 ≤ 6 * X + (-2) * Y + 0) := fun h =>
        hnot i1 (by simp) (by rw [h1]; exact mem_rtri hD7 T9_pos (by unfold ef; linarith [h.1]) (by unfold ef; linarith [h.2.1]) (by unfold ef; linarith [h.2.2]))
      have hn2 : ¬ (0 ≤ 0 * X + 4 * Y + 0 ∧ 0 ≤ (-45/8) * X + (15/8) * Y + 45 ∧ 0 ≤ (45/8) * X + (-47/8) * Y + (-45/2)) := fun h =>
        hnot i2 (by simp) (by rw [h2]; exact mem_rtri hD7 T2_pos (by unfold ef; linarith [h.1]) (by unfold ef; linarith [h.2.1]) (by unfold ef; linarith [h.2.2]))
      have hn3 : ¬ (0 ≤ (-45/8) * X + (47/8) * Y + (45/2) ∧ 0 ≤ 0 * X + (-4) * Y + (45/2) ∧ 0 ≤ (45/8) * X + (-15/8) * Y + (-45/2)) := fun h =>
        hnot i3 (by simp) (by rw [h3]; exact mem_rtri hD7 T3_pos (by unfold ef; linarith [h.1]) (by unfold ef; linarith [h.2.1]) (by unfold ef; linarith [h.2.2]))
      have hY : 0 ≤ Y := by
        by_contra hR; push_neg at hR
        linarith
      simp only [Set.mem_inter_iff, Set.mem_union, mem_halfR_rp hD7]
      refine ⟨⟨hpT', by linarith⟩, ?_⟩
      rcases le_or_gt 8 X with hX | hX
      · exact Or.inl (by linarith)
      · -- the region X < xv, Y ≥ yv
        rcases le_or_gt 0 ((-45/8) * X + (15/8) * Y + (45/2)) with hg | hg
        · -- 0 ≤ (-45/8) * X + (15/8) * Y + (45/2)
          rcases le_or_gt 0 ((45/8) * X + (-47/8) * Y + 0) with hg | hg
          · -- 0 ≤ (45/8) * X + (-47/8) * Y + 0
            exact (hn0 ⟨by linarith, by linarith, by linarith⟩).elim
          · -- (45/8) * X + (-47/8) * Y + 0 < 0
            rcases le_or_gt 0 ((-93/128) * X + (-449/128) * Y + (45/2)) with hg | hg
            · -- 0 ≤ (-93/128) * X + (-449/128) * Y + (45/2)
              exact (hn1 ⟨by linarith, by linarith, by linarith⟩).elim
            · -- (-93/128) * X + (-449/128) * Y + (45/2) < 0
              exact Or.inr (Or.inl ⟨by linarith, by linarith, by linarith⟩)
        · -- (-45/8) * X + (15/8) * Y + (45/2) < 0
          rcases le_or_gt 0 ((45/8) * X + (-47/8) * Y + 0) with hg | hg
          · -- 0 ≤ (45/8) * X + (-47/8) * Y + 0
            rcases le_or_gt 0 ((-675/128) * X + (705/128) * Y + 0) with hg | hg
            · -- 0 ≤ (-675/128) * X + (705/128) * Y + 0
              exact Or.inr (Or.inr (Or.inl ⟨by linarith, by linarith, by linarith⟩))
            · -- (-675/128) * X + (705/128) * Y + 0 < 0
              rcases le_or_gt 0 ((-93/128) * X + (-449/128) * Y + (45/2)) with hg | hg
              · -- 0 ≤ (-93/128) * X + (-449/128) * Y + (45/2)
                rcases le_or_gt 0 ((45/8) * X + (-47/8) * Y + (-45/2)) with hg | hg
                · -- 0 ≤ (45/8) * X + (-47/8) * Y + (-45/2)
                  exact (hn2 ⟨by linarith, by linarith, by linarith⟩).elim
                · -- (45/8) * X + (-47/8) * Y + (-45/2) < 0
                  exact (hn3 ⟨by linarith, by linarith, by linarith⟩).elim
              · -- (-93/128) * X + (-449/128) * Y + (45/2) < 0
                exact Or.inr (Or.inr (Or.inr (Or.inl ⟨by linarith, by linarith, by linarith, by linarith⟩)))
          · -- (45/8) * X + (-47/8) * Y + 0 < 0
            exact Or.inr (Or.inr (Or.inr (Or.inr (⟨by linarith, by linarith⟩))))
    · intro p hp
      obtain ⟨X, Y, rfl⟩ := exists_rp hD7 p
      simp only [Set.mem_inter_iff, Set.mem_union, mem_halfR_rp hD7] at hp
      obtain ⟨⟨hpT, hY⟩, hdis⟩ := hp
      obtain ⟨hT0, hT1, hT2⟩ := rtri_ef_nonneg hD7 TGT_pos hpT
      unfold ef at hT0 hT1 hT2
      refine lexLE_rp hD7 (by linarith) (fun hYe => ?_)
      rcases hdis with h | ⟨c0, c1, c2⟩ | ⟨c0, c1, c2⟩ | ⟨c0, c1, c2, c3⟩ | ⟨c0, c1⟩ <;> linarith
  have hfree : ∀ ε : ℝ, 0 < ε → ∃ t s : ℝ, 0 < t ∧ t < ε ∧ 0 < s ∧ s < ε ∧
      rp 7 8 0 + t • (rp 7 1 0 + s • perp (rp 7 1 0)) ∈ unfilled D.toDissection ([i0, i1, i2, i3] : List (Fin N)).toFinset := by
    refine hfree_of hD7 (B := 3) (by norm_num) sr7_lt (τ := (1/4)) (by norm_num) _ _ _ ?_
    intro t ht htτ
    rw [pt_ccw_rp 7 hD7, hU]
    have ht2 : t ^ 2 ≤ (1/4) * t := by nlinarith [mul_le_mul_of_nonneg_left htτ ht.le]
    have ht2p : 0 < t ^ 2 := by positivity
    exact ⟨mem_rtri hD7 TGT_pos (by unfold ef; linarith) (by unfold ef; linarith) (by unfold ef; linarith), not_mem_rtri_of_edge1 hD7 T0_pos (by unfold ef; linarith), not_mem_rtri_of_edge0 hD7 T9_pos (by unfold ef; linarith), not_mem_rtri_of_edge1 hD7 T2_pos (by unfold ef; linarith), not_mem_rtri_of_edge0 hD7 T3_pos (by unfold ef; linarith)⟩
  have hblocked : ∃ δ : ℝ, 0 < δ ∧ ∀ t s : ℝ, 0 < t → t < δ → 0 < s → s < δ →
      rp 7 8 0 + t • (rp 7 1 0 - s • perp (rp 7 1 0)) ∉ unfilled D.toDissection ([i0, i1, i2, i3] : List (Fin N)).toFinset := by
    exact hblocked_base hD7 D.toDissection _ (fun p hp => hyT p (htarget ▸ hp)) 8
  obtain ⟨j, hj, k₀, k₁, k₂, hk01, hk02, hk12, hk₀, ⟨c', hc', hk₁⟩, hk₂⟩ :=
    placement_completeness D.toDissection ([i0, i1, i2, i3] : List (Fin N)).toFinset (rp 7 8 0) (rp 7 1 0) (rp_unit hD7 (by norm_num)) hlex hfree hblocked
  have hcong : (D.tile j).Congruent MODEL := (D.tiles_congruent j).trans hmodel
  obtain ⟨hMa, hMb, hMc⟩ := MODEL_sides
  have hj0 : j ≠ i0 := fun h => hj (by rw [h]; simp)
  have hj1 : j ≠ i1 := fun h => hj (by rw [h]; simp)
  have hj2 : j ≠ i2 := fun h => hj (by rw [h]; simp)
  have hj3 : j ≠ i3 := fun h => hj (by rw [h]; simp)
  rcases six_placements hcong hMa hMb hMc (rp_unit hD7 (by norm_num)) hk01 hk02 hk12 hk₀ hc' hk₁ hk₂ with
    ⟨hP, hQ⟩ | ⟨hP, hQ⟩ | ⟨hP, hQ⟩ | ⟨hP, hQ⟩ | ⟨hP, hQ⟩ | ⟨hP, hQ⟩
  · -- placement 1: (4, 16, 15)
    have hP' : (D.tile j).pts k₁ = rp 7 12 0 := by rw [hP, rp_add_smul]; norm_num
    have hQ' : (D.tile j).pts k₂ = rp 7 (111/8) (45/8) := by
      rw [hQ, placeThird_rp hD7 8 0 1 0 4 16 15 (47/8) (45/8) (by norm_num) (by norm_num) (by norm_num)]; norm_num
    exact (escape_of D.toDissection htarget j k₂ hQ' (not_mem_rtri_of_edge1 hD7 TGT_pos (by unfold ef; norm_num)))
  · -- placement 2: (16, 4, 15)
    have hP' : (D.tile j).pts k₁ = rp 7 24 0 := by rw [hP, rp_add_smul]; norm_num
    have hQ' : (D.tile j).pts k₂ = rp 7 (303/32) (45/32) := by
      rw [hQ, placeThird_rp hD7 8 0 1 0 16 4 15 (47/32) (45/32) (by norm_num) (by norm_num) (by norm_num)]; norm_num
    exact (escape_of D.toDissection htarget j k₁ hP' (not_mem_rtri_of_edge1 hD7 TGT_pos (by unfold ef; norm_num)))
  · -- placement 3: (4, 15, 16)
    have hP' : (D.tile j).pts k₁ = rp 7 12 0 := by rw [hP, rp_add_smul]; norm_num
    have hQ' : (D.tile j).pts k₂ = rp 7 (49/8) (45/8) := by
      rw [hQ, placeThird_rp hD7 8 0 1 0 4 15 16 (-15/8) (45/8) (by norm_num) (by norm_num) (by norm_num)]; norm_num
    have hjc : (D.tile j).carrier = T4.carrier :=
      carrier_eq_rtri_of_pts hD7 _ hk01 hk02 hk12 hk₀ hP' hQ' T4_pos
    exact (overlap_of D.toDissection hj2.symm h2 hjc (w := rp 7 8 (3510/1457))
      (mem_interior_rtri hD7 T2_pos (by unfold ef; norm_num) (by unfold ef; norm_num) (by unfold ef; norm_num))
      (mem_interior_rtri hD7 T4_pos (by unfold ef; norm_num) (by unfold ef; norm_num) (by unfold ef; norm_num)))
  · -- placement 4: (15, 4, 16)
    have hP' : (D.tile j).pts k₁ = rp 7 23 0 := by rw [hP, rp_add_smul]; norm_num
    have hQ' : (D.tile j).pts k₂ = rp 7 (15/2) (3/2) := by
      rw [hQ, placeThird_rp hD7 8 0 1 0 15 4 16 (-1/2) (3/2) (by norm_num) (by norm_num) (by norm_num)]; norm_num
    exact (escape_of D.toDissection htarget j k₁ hP' (not_mem_rtri_of_edge1 hD7 TGT_pos (by unfold ef; norm_num)))
  · -- placement 5: (16, 15, 4)
    have hP' : (D.tile j).pts k₁ = rp 7 24 0 := by rw [hP, rp_add_smul]; norm_num
    have hQ' : (D.tile j).pts k₂ = rp 7 (721/32) (45/32) := by
      rw [hQ, placeThird_rp hD7 8 0 1 0 16 15 4 (465/32) (45/32) (by norm_num) (by norm_num) (by norm_num)]; norm_num
    exact (escape_of D.toDissection htarget j k₂ hQ' (not_mem_rtri_of_edge1 hD7 TGT_pos (by unfold ef; norm_num)))
  · -- placement 6: (15, 16, 4)
    have hP' : (D.tile j).pts k₁ = rp 7 23 0 := by rw [hP, rp_add_smul]; norm_num
    have hQ' : (D.tile j).pts k₂ = rp 7 (47/2) (3/2) := by
      rw [hQ, placeThird_rp hD7 8 0 1 0 15 16 4 (31/2) (3/2) (by norm_num) (by norm_num) (by norm_num)]; norm_num
    exact (escape_of D.toDissection htarget j k₂ hQ' (not_mem_rtri_of_edge1 hD7 TGT_pos (by unfold ef; norm_num)))

/-- Node 9: 4 placed tile(s), `v = (8, 0)`, `d = (1, 0)`; kills: escape(Q, edge 1), escape(P, edge 1), overlap(tile 2), escape(P, edge 1), escape(Q, edge 1), escape(Q, edge 1). -/
theorem node_9 {N : ℕ} (D : CongruentDissection N)
    (htarget : D.target.carrier = TGT.carrier) (hmodel : D.model.Congruent MODEL)
    (i0 i1 i2 i3 : Fin N) (h0 : (D.tile i0).carrier = T0.carrier) (h1 : (D.tile i1).carrier = T9.carrier) (h2 : (D.tile i2).carrier = T2.carrier) (h3 : (D.tile i3).carrier = T5.carrier)
    : False := by
  classical
  have hyT : ∀ p ∈ TGT.carrier, 0 ≤ p 1 := fun p hp => target_y_nonneg hD7 (by norm_num) TGT_pos hp
  have hU : ∀ p, p ∈ unfilled D.toDissection ([i0, i1, i2, i3] : List (Fin N)).toFinset ↔ p ∈ TGT.carrier ∧ p ∉ T0.carrier ∧ p ∉ T9.carrier ∧ p ∉ T2.carrier ∧ p ∉ T5.carrier := by
    intro p; rw [mem_unfilled_iff, htarget]
    simp [h0, h1, h2, h3]
  have hlex : ∀ p ∈ closure (unfilled D.toDissection ([i0, i1, i2, i3] : List (Fin N)).toFinset), LexLE (rp 7 8 0) p := by
    refine hlex_of D.toDissection _ _ ((TGT.carrier ∩ halfR 7 0 1 0) ∩ (halfR 7 1 0 (-8) ∪ ((halfR 7 (-45/8) (15/8) (45/2) ∩ (halfR 7 (-45/8) (47/8) 0 ∩ (halfR 7 (93/128) (449/128) (-45/2)))) ∪ ((halfR 7 (45/8) (-15/8) (-45/2) ∩ (halfR 7 (45/8) (-47/8) 0 ∩ (halfR 7 (-675/128) (705/128) 0))) ∪ ((halfR 7 (45/8) (-15/8) (-45/2) ∩ (halfR 7 (45/8) (-47/8) 0 ∩ (halfR 7 (675/128) (-705/128) 0 ∩ (halfR 7 (93/128) (449/128) (-45/2))))) ∪ ((halfR 7 (45/8) (-15/8) (-45/2) ∩ (halfR 7 (-45/8) (47/8) 0)))))))) ((TGT.isCompact.isClosed.inter (isClosed_halfR _ _ _ _)).inter ((isClosed_halfR _ _ _ _).union (((isClosed_halfR _ _ _ _).inter ((isClosed_halfR _ _ _ _).inter (isClosed_halfR _ _ _ _))).union (((isClosed_halfR _ _ _ _).inter ((isClosed_halfR _ _ _ _).inter (isClosed_halfR _ _ _ _))).union (((isClosed_halfR _ _ _ _).inter ((isClosed_halfR _ _ _ _).inter ((isClosed_halfR _ _ _ _).inter (isClosed_halfR _ _ _ _)))).union ((isClosed_halfR _ _ _ _).inter (isClosed_halfR _ _ _ _))))))) ?_ ?_
    · intro p hpT hnot
      obtain ⟨X, Y, rfl⟩ := exists_rp hD7 p
      have hpT' : rp 7 X Y ∈ TGT.carrier := htarget ▸ hpT
      obtain ⟨hT0, hT1, hT2⟩ := rtri_ef_nonneg hD7 TGT_pos hpT'
      unfold ef at hT0 hT1 hT2
      have hn0 : ¬ (0 ≤ 0 * X + 4 * Y + 0 ∧ 0 ≤ (-45/8) * X + (15/8) * Y + (45/2) ∧ 0 ≤ (45/8) * X + (-47/8) * Y + 0) := fun h =>
        hnot i0 (by simp) (by rw [h0]; exact mem_rtri hD7 T0_pos (by unfold ef; linarith [h.1]) (by unfold ef; linarith [h.2.1]) (by unfold ef; linarith [h.2.2]))
      have hn1 : ¬ (0 ≤ (-675/128) * X + (705/128) * Y + 0 ∧ 0 ≤ (-93/128) * X + (-449/128) * Y + (45/2) ∧ 0 ≤ 6 * X + (-2) * Y + 0) := fun h =>
        hnot i1 (by simp) (by rw [h1]; exact mem_rtri hD7 T9_pos (by unfold ef; linarith [h.1]) (by unfold ef; linarith [h.2.1]) (by unfold ef; linarith [h.2.2]))
      have hn2 : ¬ (0 ≤ 0 * X + 4 * Y + 0 ∧ 0 ≤ (-45/8) * X + (15/8) * Y + 45 ∧ 0 ≤ (45/8) * X + (-47/8) * Y + (-45/2)) := fun h =>
        hnot i2 (by simp) (by rw [h2]; exact mem_rtri hD7 T2_pos (by unfold ef; linarith [h.1]) (by unfold ef; linarith [h.2.1]) (by unfold ef; linarith [h.2.2]))
      have hn3 : ¬ (0 ≤ (-675/128) * X + (705/128) * Y + (675/32) ∧ 0 ≤ (-93/128) * X + (-449/128) * Y + (813/32) ∧ 0 ≤ 6 * X + (-2) * Y + (-24)) := fun h =>
        hnot i3 (by simp) (by rw [h3]; exact mem_rtri hD7 T5_pos (by unfold ef; linarith [h.1]) (by unfold ef; linarith [h.2.1]) (by unfold ef; linarith [h.2.2]))
      have hY : 0 ≤ Y := by
        by_contra hR; push_neg at hR
        linarith
      simp only [Set.mem_inter_iff, Set.mem_union, mem_halfR_rp hD7]
      refine ⟨⟨hpT', by linarith⟩, ?_⟩
      rcases le_or_gt 8 X with hX | hX
      · exact Or.inl (by linarith)
      · -- the region X < xv, Y ≥ yv
        rcases le_or_gt 0 ((-45/8) * X + (15/8) * Y + (45/2)) with hg | hg
        · -- 0 ≤ (-45/8) * X + (15/8) * Y + (45/2)
          rcases le_or_gt 0 ((45/8) * X + (-47/8) * Y + 0) with hg | hg
          · -- 0 ≤ (45/8) * X + (-47/8) * Y + 0
            exact (hn0 ⟨by linarith, by linarith, by linarith⟩).elim
          · -- (45/8) * X + (-47/8) * Y + 0 < 0
            rcases le_or_gt 0 ((-93/128) * X + (-449/128) * Y + (45/2)) with hg | hg
            · -- 0 ≤ (-93/128) * X + (-449/128) * Y + (45/2)
              exact (hn1 ⟨by linarith, by linarith, by linarith⟩).elim
            · -- (-93/128) * X + (-449/128) * Y + (45/2) < 0
              exact Or.inr (Or.inl ⟨by linarith, by linarith, by linarith⟩)
        · -- (-45/8) * X + (15/8) * Y + (45/2) < 0
          rcases le_or_gt 0 ((45/8) * X + (-47/8) * Y + 0) with hg | hg
          · -- 0 ≤ (45/8) * X + (-47/8) * Y + 0
            rcases le_or_gt 0 ((-675/128) * X + (705/128) * Y + 0) with hg | hg
            · -- 0 ≤ (-675/128) * X + (705/128) * Y + 0
              exact Or.inr (Or.inr (Or.inl ⟨by linarith, by linarith, by linarith⟩))
            · -- (-675/128) * X + (705/128) * Y + 0 < 0
              rcases le_or_gt 0 ((-93/128) * X + (-449/128) * Y + (45/2)) with hg | hg
              · -- 0 ≤ (-93/128) * X + (-449/128) * Y + (45/2)
                rcases le_or_gt 0 ((45/8) * X + (-47/8) * Y + (-45/2)) with hg | hg
                · -- 0 ≤ (45/8) * X + (-47/8) * Y + (-45/2)
                  exact (hn2 ⟨by linarith, by linarith, by linarith⟩).elim
                · -- (45/8) * X + (-47/8) * Y + (-45/2) < 0
                  exact (hn3 ⟨by linarith, by linarith, by linarith⟩).elim
              · -- (-93/128) * X + (-449/128) * Y + (45/2) < 0
                exact Or.inr (Or.inr (Or.inr (Or.inl ⟨by linarith, by linarith, by linarith, by linarith⟩)))
          · -- (45/8) * X + (-47/8) * Y + 0 < 0
            exact Or.inr (Or.inr (Or.inr (Or.inr (⟨by linarith, by linarith⟩))))
    · intro p hp
      obtain ⟨X, Y, rfl⟩ := exists_rp hD7 p
      simp only [Set.mem_inter_iff, Set.mem_union, mem_halfR_rp hD7] at hp
      obtain ⟨⟨hpT, hY⟩, hdis⟩ := hp
      obtain ⟨hT0, hT1, hT2⟩ := rtri_ef_nonneg hD7 TGT_pos hpT
      unfold ef at hT0 hT1 hT2
      refine lexLE_rp hD7 (by linarith) (fun hYe => ?_)
      rcases hdis with h | ⟨c0, c1, c2⟩ | ⟨c0, c1, c2⟩ | ⟨c0, c1, c2, c3⟩ | ⟨c0, c1⟩ <;> linarith
  have hfree : ∀ ε : ℝ, 0 < ε → ∃ t s : ℝ, 0 < t ∧ t < ε ∧ 0 < s ∧ s < ε ∧
      rp 7 8 0 + t • (rp 7 1 0 + s • perp (rp 7 1 0)) ∈ unfilled D.toDissection ([i0, i1, i2, i3] : List (Fin N)).toFinset := by
    refine hfree_of hD7 (B := 3) (by norm_num) sr7_lt (τ := (1/4)) (by norm_num) _ _ _ ?_
    intro t ht htτ
    rw [pt_ccw_rp 7 hD7, hU]
    have ht2 : t ^ 2 ≤ (1/4) * t := by nlinarith [mul_le_mul_of_nonneg_left htτ ht.le]
    have ht2p : 0 < t ^ 2 := by positivity
    exact ⟨mem_rtri hD7 TGT_pos (by unfold ef; linarith) (by unfold ef; linarith) (by unfold ef; linarith), not_mem_rtri_of_edge1 hD7 T0_pos (by unfold ef; linarith), not_mem_rtri_of_edge0 hD7 T9_pos (by unfold ef; linarith), not_mem_rtri_of_edge1 hD7 T2_pos (by unfold ef; linarith), not_mem_rtri_of_edge0 hD7 T5_pos (by unfold ef; linarith)⟩
  have hblocked : ∃ δ : ℝ, 0 < δ ∧ ∀ t s : ℝ, 0 < t → t < δ → 0 < s → s < δ →
      rp 7 8 0 + t • (rp 7 1 0 - s • perp (rp 7 1 0)) ∉ unfilled D.toDissection ([i0, i1, i2, i3] : List (Fin N)).toFinset := by
    exact hblocked_base hD7 D.toDissection _ (fun p hp => hyT p (htarget ▸ hp)) 8
  obtain ⟨j, hj, k₀, k₁, k₂, hk01, hk02, hk12, hk₀, ⟨c', hc', hk₁⟩, hk₂⟩ :=
    placement_completeness D.toDissection ([i0, i1, i2, i3] : List (Fin N)).toFinset (rp 7 8 0) (rp 7 1 0) (rp_unit hD7 (by norm_num)) hlex hfree hblocked
  have hcong : (D.tile j).Congruent MODEL := (D.tiles_congruent j).trans hmodel
  obtain ⟨hMa, hMb, hMc⟩ := MODEL_sides
  have hj0 : j ≠ i0 := fun h => hj (by rw [h]; simp)
  have hj1 : j ≠ i1 := fun h => hj (by rw [h]; simp)
  have hj2 : j ≠ i2 := fun h => hj (by rw [h]; simp)
  have hj3 : j ≠ i3 := fun h => hj (by rw [h]; simp)
  rcases six_placements hcong hMa hMb hMc (rp_unit hD7 (by norm_num)) hk01 hk02 hk12 hk₀ hc' hk₁ hk₂ with
    ⟨hP, hQ⟩ | ⟨hP, hQ⟩ | ⟨hP, hQ⟩ | ⟨hP, hQ⟩ | ⟨hP, hQ⟩ | ⟨hP, hQ⟩
  · -- placement 1: (4, 16, 15)
    have hP' : (D.tile j).pts k₁ = rp 7 12 0 := by rw [hP, rp_add_smul]; norm_num
    have hQ' : (D.tile j).pts k₂ = rp 7 (111/8) (45/8) := by
      rw [hQ, placeThird_rp hD7 8 0 1 0 4 16 15 (47/8) (45/8) (by norm_num) (by norm_num) (by norm_num)]; norm_num
    exact (escape_of D.toDissection htarget j k₂ hQ' (not_mem_rtri_of_edge1 hD7 TGT_pos (by unfold ef; norm_num)))
  · -- placement 2: (16, 4, 15)
    have hP' : (D.tile j).pts k₁ = rp 7 24 0 := by rw [hP, rp_add_smul]; norm_num
    have hQ' : (D.tile j).pts k₂ = rp 7 (303/32) (45/32) := by
      rw [hQ, placeThird_rp hD7 8 0 1 0 16 4 15 (47/32) (45/32) (by norm_num) (by norm_num) (by norm_num)]; norm_num
    exact (escape_of D.toDissection htarget j k₁ hP' (not_mem_rtri_of_edge1 hD7 TGT_pos (by unfold ef; norm_num)))
  · -- placement 3: (4, 15, 16)
    have hP' : (D.tile j).pts k₁ = rp 7 12 0 := by rw [hP, rp_add_smul]; norm_num
    have hQ' : (D.tile j).pts k₂ = rp 7 (49/8) (45/8) := by
      rw [hQ, placeThird_rp hD7 8 0 1 0 4 15 16 (-15/8) (45/8) (by norm_num) (by norm_num) (by norm_num)]; norm_num
    have hjc : (D.tile j).carrier = T4.carrier :=
      carrier_eq_rtri_of_pts hD7 _ hk01 hk02 hk12 hk₀ hP' hQ' T4_pos
    exact (overlap_of D.toDissection hj2.symm h2 hjc (w := rp 7 8 (3510/1457))
      (mem_interior_rtri hD7 T2_pos (by unfold ef; norm_num) (by unfold ef; norm_num) (by unfold ef; norm_num))
      (mem_interior_rtri hD7 T4_pos (by unfold ef; norm_num) (by unfold ef; norm_num) (by unfold ef; norm_num)))
  · -- placement 4: (15, 4, 16)
    have hP' : (D.tile j).pts k₁ = rp 7 23 0 := by rw [hP, rp_add_smul]; norm_num
    have hQ' : (D.tile j).pts k₂ = rp 7 (15/2) (3/2) := by
      rw [hQ, placeThird_rp hD7 8 0 1 0 15 4 16 (-1/2) (3/2) (by norm_num) (by norm_num) (by norm_num)]; norm_num
    exact (escape_of D.toDissection htarget j k₁ hP' (not_mem_rtri_of_edge1 hD7 TGT_pos (by unfold ef; norm_num)))
  · -- placement 5: (16, 15, 4)
    have hP' : (D.tile j).pts k₁ = rp 7 24 0 := by rw [hP, rp_add_smul]; norm_num
    have hQ' : (D.tile j).pts k₂ = rp 7 (721/32) (45/32) := by
      rw [hQ, placeThird_rp hD7 8 0 1 0 16 15 4 (465/32) (45/32) (by norm_num) (by norm_num) (by norm_num)]; norm_num
    exact (escape_of D.toDissection htarget j k₂ hQ' (not_mem_rtri_of_edge1 hD7 TGT_pos (by unfold ef; norm_num)))
  · -- placement 6: (15, 16, 4)
    have hP' : (D.tile j).pts k₁ = rp 7 23 0 := by rw [hP, rp_add_smul]; norm_num
    have hQ' : (D.tile j).pts k₂ = rp 7 (47/2) (3/2) := by
      rw [hQ, placeThird_rp hD7 8 0 1 0 15 16 4 (31/2) (3/2) (by norm_num) (by norm_num) (by norm_num)]; norm_num
    exact (escape_of D.toDissection htarget j k₂ hQ' (not_mem_rtri_of_edge1 hD7 TGT_pos (by unfold ef; norm_num)))

/-- Node 7: 3 placed tile(s), `v = (4, 0)`, `d = (47/128, 45/128·r)`; kills: escape(Q, edge 2), overlap(tile 0), escape(Q, edge 2), overlap(tile 0), child 8, child 9. -/
theorem node_7 {N : ℕ} (D : CongruentDissection N)
    (htarget : D.target.carrier = TGT.carrier) (hmodel : D.model.Congruent MODEL)
    (i0 i1 i2 : Fin N) (h0 : (D.tile i0).carrier = T0.carrier) (h1 : (D.tile i1).carrier = T9.carrier) (h2 : (D.tile i2).carrier = T2.carrier)
    : False := by
  classical
  have hyT : ∀ p ∈ TGT.carrier, 0 ≤ p 1 := fun p hp => target_y_nonneg hD7 (by norm_num) TGT_pos hp
  have hU : ∀ p, p ∈ unfilled D.toDissection ([i0, i1, i2] : List (Fin N)).toFinset ↔ p ∈ TGT.carrier ∧ p ∉ T0.carrier ∧ p ∉ T9.carrier ∧ p ∉ T2.carrier := by
    intro p; rw [mem_unfilled_iff, htarget]
    simp [h0, h1, h2]
  have hlex : ∀ p ∈ closure (unfilled D.toDissection ([i0, i1, i2] : List (Fin N)).toFinset), LexLE (rp 7 4 0) p := by
    refine hlex_of D.toDissection _ _ ((TGT.carrier ∩ halfR 7 0 1 0) ∩ (halfR 7 1 0 (-4) ∪ ((halfR 7 (-45/8) (47/8) 0 ∩ (halfR 7 (93/128) (449/128) (-45/2)))))) ((TGT.isCompact.isClosed.inter (isClosed_halfR _ _ _ _)).inter ((isClosed_halfR _ _ _ _).union ((isClosed_halfR _ _ _ _).inter (isClosed_halfR _ _ _ _)))) ?_ ?_
    · intro p hpT hnot
      obtain ⟨X, Y, rfl⟩ := exists_rp hD7 p
      have hpT' : rp 7 X Y ∈ TGT.carrier := htarget ▸ hpT
      obtain ⟨hT0, hT1, hT2⟩ := rtri_ef_nonneg hD7 TGT_pos hpT'
      unfold ef at hT0 hT1 hT2
      have hn0 : ¬ (0 ≤ 0 * X + 4 * Y + 0 ∧ 0 ≤ (-45/8) * X + (15/8) * Y + (45/2) ∧ 0 ≤ (45/8) * X + (-47/8) * Y + 0) := fun h =>
        hnot i0 (by simp) (by rw [h0]; exact mem_rtri hD7 T0_pos (by unfold ef; linarith [h.1]) (by unfold ef; linarith [h.2.1]) (by unfold ef; linarith [h.2.2]))
      have hn1 : ¬ (0 ≤ (-675/128) * X + (705/128) * Y + 0 ∧ 0 ≤ (-93/128) * X + (-449/128) * Y + (45/2) ∧ 0 ≤ 6 * X + (-2) * Y + 0) := fun h =>
        hnot i1 (by simp) (by rw [h1]; exact mem_rtri hD7 T9_pos (by unfold ef; linarith [h.1]) (by unfold ef; linarith [h.2.1]) (by unfold ef; linarith [h.2.2]))
      have hn2 : ¬ (0 ≤ 0 * X + 4 * Y + 0 ∧ 0 ≤ (-45/8) * X + (15/8) * Y + 45 ∧ 0 ≤ (45/8) * X + (-47/8) * Y + (-45/2)) := fun h =>
        hnot i2 (by simp) (by rw [h2]; exact mem_rtri hD7 T2_pos (by unfold ef; linarith [h.1]) (by unfold ef; linarith [h.2.1]) (by unfold ef; linarith [h.2.2]))
      have hY : 0 ≤ Y := by
        by_contra hR; push_neg at hR
        linarith
      simp only [Set.mem_inter_iff, Set.mem_union, mem_halfR_rp hD7]
      refine ⟨⟨hpT', by linarith⟩, ?_⟩
      rcases le_or_gt 4 X with hX | hX
      · exact Or.inl (by linarith)
      · -- the region X < xv, Y ≥ yv
        rcases le_or_gt 0 ((45/8) * X + (-47/8) * Y + 0) with hg | hg
        · -- 0 ≤ (45/8) * X + (-47/8) * Y + 0
          exact (hn0 ⟨by linarith, by linarith, by linarith⟩).elim
        · -- (45/8) * X + (-47/8) * Y + 0 < 0
          rcases le_or_gt 0 ((-93/128) * X + (-449/128) * Y + (45/2)) with hg | hg
          · -- 0 ≤ (-93/128) * X + (-449/128) * Y + (45/2)
            exact (hn1 ⟨by linarith, by linarith, by linarith⟩).elim
          · -- (-93/128) * X + (-449/128) * Y + (45/2) < 0
            exact Or.inr (⟨by linarith, by linarith⟩)
    · intro p hp
      obtain ⟨X, Y, rfl⟩ := exists_rp hD7 p
      simp only [Set.mem_inter_iff, Set.mem_union, mem_halfR_rp hD7] at hp
      obtain ⟨⟨hpT, hY⟩, hdis⟩ := hp
      obtain ⟨hT0, hT1, hT2⟩ := rtri_ef_nonneg hD7 TGT_pos hpT
      unfold ef at hT0 hT1 hT2
      refine lexLE_rp hD7 (by linarith) (fun hYe => ?_)
      rcases hdis with h | ⟨c0, c1⟩ <;> linarith
  have hfree : ∀ ε : ℝ, 0 < ε → ∃ t s : ℝ, 0 < t ∧ t < ε ∧ 0 < s ∧ s < ε ∧
      rp 7 4 0 + t • (rp 7 (47/128) (45/128) + s • perp (rp 7 (47/128) (45/128))) ∈ unfilled D.toDissection ([i0, i1, i2] : List (Fin N)).toFinset := by
    refine hfree_of hD7 (B := 3) (by norm_num) sr7_lt (τ := (1/16)) (by norm_num) _ _ _ ?_
    intro t ht htτ
    rw [pt_ccw_rp 7 hD7, hU]
    have ht2 : t ^ 2 ≤ (1/16) * t := by nlinarith [mul_le_mul_of_nonneg_left htτ ht.le]
    have ht2p : 0 < t ^ 2 := by positivity
    exact ⟨mem_rtri hD7 TGT_pos (by unfold ef; linarith) (by unfold ef; linarith) (by unfold ef; linarith), not_mem_rtri_of_edge1 hD7 T0_pos (by unfold ef; linarith), not_mem_rtri_of_edge0 hD7 T9_pos (by unfold ef; linarith), not_mem_rtri_of_edge2 hD7 T2_pos (by unfold ef; linarith)⟩
  have hblocked : ∃ δ : ℝ, 0 < δ ∧ ∀ t s : ℝ, 0 < t → t < δ → 0 < s → s < δ →
      rp 7 4 0 + t • (rp 7 (47/128) (45/128) - s • perp (rp 7 (47/128) (45/128))) ∉ unfilled D.toDissection ([i0, i1, i2] : List (Fin N)).toFinset := by
    have hsub : T2.carrier ⊆ (D.tile i2).carrier := (h2.trans
      (carrier_eq_rtri_of_pts hD7 T2 (k₀ := 0) (k₁ := 1) (k₂ := 2) (by decide) (by decide) (by decide) rfl rfl rfl T2_pos)).symm.subset
    refine hblocked_of_wedge hD7 sr7_gt1 D.toDissection _ (i := i2) (by simp) _ _ T2 hsub rfl
      (wedge_interior T2 (rp 7 (47/128) (45/128)) (sr 7 • perp (rp 7 (47/128) (45/128))) 0 (1/16) (-32/45) (47/720) ?_ ?_ ?_ ?_)
    · rw [T2_pts.1, T2_pts.2.1, T2_pts.2.2]; refine plane_ext ?_ ?_ <;> simp <;> ring
    · rw [sr_smul_perp_rp hD7, T2_pts.1, T2_pts.2.1, T2_pts.2.2]; refine plane_ext ?_ ?_ <;> simp <;> ring
    · exact Or.inr ⟨by norm_num, by norm_num⟩
    · exact Or.inl (by norm_num)
  obtain ⟨j, hj, k₀, k₁, k₂, hk01, hk02, hk12, hk₀, ⟨c', hc', hk₁⟩, hk₂⟩ :=
    placement_completeness D.toDissection ([i0, i1, i2] : List (Fin N)).toFinset (rp 7 4 0) (rp 7 (47/128) (45/128)) (rp_unit hD7 (by norm_num)) hlex hfree hblocked
  have hcong : (D.tile j).Congruent MODEL := (D.tiles_congruent j).trans hmodel
  obtain ⟨hMa, hMb, hMc⟩ := MODEL_sides
  have hj0 : j ≠ i0 := fun h => hj (by rw [h]; simp)
  have hj1 : j ≠ i1 := fun h => hj (by rw [h]; simp)
  have hj2 : j ≠ i2 := fun h => hj (by rw [h]; simp)
  rcases six_placements hcong hMa hMb hMc (rp_unit hD7 (by norm_num)) hk01 hk02 hk12 hk₀ hc' hk₁ hk₂ with
    ⟨hP, hQ⟩ | ⟨hP, hQ⟩ | ⟨hP, hQ⟩ | ⟨hP, hQ⟩ | ⟨hP, hQ⟩ | ⟨hP, hQ⟩
  · -- placement 1: (4, 16, 15)
    have hP' : (D.tile j).pts k₁ = rp 7 (175/32) (45/32) := by rw [hP, rp_add_smul]; norm_num
    have hQ' : (D.tile j).pts k₂ = rp 7 (-3935/512) (2115/512) := by
      rw [hQ, placeThird_rp hD7 4 0 (47/128) (45/128) 4 16 15 (47/8) (45/8) (by norm_num) (by norm_num) (by norm_num)]; norm_num
    exact (escape_of D.toDissection htarget j k₂ hQ' (not_mem_rtri_of_edge2 hD7 TGT_pos (by unfold ef; norm_num)))
  · -- placement 2: (16, 4, 15)
    have hP' : (D.tile j).pts k₁ = rp 7 (79/8) (45/8) := by rw [hP, rp_add_smul]; norm_num
    have hQ' : (D.tile j).pts k₂ = rp 7 (2209/2048) (2115/2048) := by
      rw [hQ, placeThird_rp hD7 4 0 (47/128) (45/128) 16 4 15 (47/32) (45/32) (by norm_num) (by norm_num) (by norm_num)]; norm_num
    have hjc : (D.tile j).carrier = T6.carrier :=
      carrier_eq_rtri_of_pts hD7 _ hk01 hk02 hk12 hk₀ hP' hQ' T6_pos
    exact (overlap_of D.toDissection hj0.symm h0 hjc (w := rp 7 (213973/63488) (87391/63488))
      (mem_interior_rtri hD7 T0_pos (by unfold ef; norm_num) (by unfold ef; norm_num) (by unfold ef; norm_num))
      (mem_interior_rtri hD7 T6_pos (by unfold ef; norm_num) (by unfold ef; norm_num) (by unfold ef; norm_num)))
  · -- placement 3: (4, 15, 16)
    have hP' : (D.tile j).pts k₁ = rp 7 (175/32) (45/32) := by rw [hP, rp_add_smul]; norm_num
    have hQ' : (D.tile j).pts k₂ = rp 7 (-337/32) (45/32) := by
      rw [hQ, placeThird_rp hD7 4 0 (47/128) (45/128) 4 15 16 (-15/8) (45/8) (by norm_num) (by norm_num) (by norm_num)]; norm_num
    exact (escape_of D.toDissection htarget j k₂ hQ' (not_mem_rtri_of_edge2 hD7 TGT_pos (by unfold ef; norm_num)))
  · -- placement 4: (15, 4, 16)
    have hP' : (D.tile j).pts k₁ = rp 7 (1217/128) (675/128) := by rw [hP, rp_add_smul]; norm_num
    have hQ' : (D.tile j).pts k₂ = rp 7 (1/8) (3/8) := by
      rw [hQ, placeThird_rp hD7 4 0 (47/128) (45/128) 15 4 16 (-1/2) (3/2) (by norm_num) (by norm_num) (by norm_num)]; norm_num
    have hjc : (D.tile j).carrier = T7.carrier :=
      carrier_eq_rtri_of_pts hD7 _ hk01 hk02 hk12 hk₀ hP' hQ' T7_pos
    exact (overlap_of D.toDissection hj0.symm h0 hjc (w := rp 7 (637823/253952) (249885/253952))
      (mem_interior_rtri hD7 T0_pos (by unfold ef; norm_num) (by unfold ef; norm_num) (by unfold ef; norm_num))
      (mem_interior_rtri hD7 T7_pos (by unfold ef; norm_num) (by unfold ef; norm_num) (by unfold ef; norm_num)))
  · -- placement 5: (16, 15, 4)
    have hP' : (D.tile j).pts k₁ = rp 7 (79/8) (45/8) := by rw [hP, rp_add_smul]; norm_num
    have hQ' : (D.tile j).pts k₂ = rp 7 (47/8) (45/8) := by
      rw [hQ, placeThird_rp hD7 4 0 (47/128) (45/128) 16 15 4 (465/32) (45/32) (by norm_num) (by norm_num) (by norm_num)]; norm_num
    have hjc : (D.tile j).carrier = T3.carrier :=
      carrier_eq_rtri_of_pts hD7 _ hk01 hk02 hk12 hk₀ hP' hQ' T3_pos
    exact node_8 D htarget hmodel i0 i1 i2 j h0 h1 h2 hjc
  · -- placement 6: (15, 16, 4)
    have hP' : (D.tile j).pts k₁ = rp 7 (1217/128) (675/128) := by rw [hP, rp_add_smul]; norm_num
    have hQ' : (D.tile j).pts k₂ = rp 7 6 6 := by
      rw [hQ, placeThird_rp hD7 4 0 (47/128) (45/128) 15 16 4 (31/2) (3/2) (by norm_num) (by norm_num) (by norm_num)]; norm_num
    have hjc : (D.tile j).carrier = T5.carrier :=
      carrier_eq_rtri_of_pts hD7 _ hk01 hk02 hk12 hk₀ hP' hQ' T5_pos
    exact node_9 D htarget hmodel i0 i1 i2 j h0 h1 h2 hjc

/-- Node 6: 2 placed tile(s), `v = (4, 0)`, `d = (1, 0)`; kills: child 7, escape(P, edge 1), overlap(tile 0), escape(P, edge 1), escape(Q, edge 1), escape(Q, edge 1). -/
theorem node_6 {N : ℕ} (D : CongruentDissection N)
    (htarget : D.target.carrier = TGT.carrier) (hmodel : D.model.Congruent MODEL)
    (i0 i1 : Fin N) (h0 : (D.tile i0).carrier = T0.carrier) (h1 : (D.tile i1).carrier = T9.carrier)
    : False := by
  classical
  have hyT : ∀ p ∈ TGT.carrier, 0 ≤ p 1 := fun p hp => target_y_nonneg hD7 (by norm_num) TGT_pos hp
  have hU : ∀ p, p ∈ unfilled D.toDissection ([i0, i1] : List (Fin N)).toFinset ↔ p ∈ TGT.carrier ∧ p ∉ T0.carrier ∧ p ∉ T9.carrier := by
    intro p; rw [mem_unfilled_iff, htarget]
    simp [h0, h1]
  have hlex : ∀ p ∈ closure (unfilled D.toDissection ([i0, i1] : List (Fin N)).toFinset), LexLE (rp 7 4 0) p := by
    refine hlex_of D.toDissection _ _ ((TGT.carrier ∩ halfR 7 0 1 0) ∩ (halfR 7 1 0 (-4) ∪ ((halfR 7 (-45/8) (47/8) 0 ∩ (halfR 7 (93/128) (449/128) (-45/2)))))) ((TGT.isCompact.isClosed.inter (isClosed_halfR _ _ _ _)).inter ((isClosed_halfR _ _ _ _).union ((isClosed_halfR _ _ _ _).inter (isClosed_halfR _ _ _ _)))) ?_ ?_
    · intro p hpT hnot
      obtain ⟨X, Y, rfl⟩ := exists_rp hD7 p
      have hpT' : rp 7 X Y ∈ TGT.carrier := htarget ▸ hpT
      obtain ⟨hT0, hT1, hT2⟩ := rtri_ef_nonneg hD7 TGT_pos hpT'
      unfold ef at hT0 hT1 hT2
      have hn0 : ¬ (0 ≤ 0 * X + 4 * Y + 0 ∧ 0 ≤ (-45/8) * X + (15/8) * Y + (45/2) ∧ 0 ≤ (45/8) * X + (-47/8) * Y + 0) := fun h =>
        hnot i0 (by simp) (by rw [h0]; exact mem_rtri hD7 T0_pos (by unfold ef; linarith [h.1]) (by unfold ef; linarith [h.2.1]) (by unfold ef; linarith [h.2.2]))
      have hn1 : ¬ (0 ≤ (-675/128) * X + (705/128) * Y + 0 ∧ 0 ≤ (-93/128) * X + (-449/128) * Y + (45/2) ∧ 0 ≤ 6 * X + (-2) * Y + 0) := fun h =>
        hnot i1 (by simp) (by rw [h1]; exact mem_rtri hD7 T9_pos (by unfold ef; linarith [h.1]) (by unfold ef; linarith [h.2.1]) (by unfold ef; linarith [h.2.2]))
      have hY : 0 ≤ Y := by
        by_contra hR; push_neg at hR
        linarith
      simp only [Set.mem_inter_iff, Set.mem_union, mem_halfR_rp hD7]
      refine ⟨⟨hpT', by linarith⟩, ?_⟩
      rcases le_or_gt 4 X with hX | hX
      · exact Or.inl (by linarith)
      · -- the region X < xv, Y ≥ yv
        rcases le_or_gt 0 ((45/8) * X + (-47/8) * Y + 0) with hg | hg
        · -- 0 ≤ (45/8) * X + (-47/8) * Y + 0
          exact (hn0 ⟨by linarith, by linarith, by linarith⟩).elim
        · -- (45/8) * X + (-47/8) * Y + 0 < 0
          rcases le_or_gt 0 ((-93/128) * X + (-449/128) * Y + (45/2)) with hg | hg
          · -- 0 ≤ (-93/128) * X + (-449/128) * Y + (45/2)
            exact (hn1 ⟨by linarith, by linarith, by linarith⟩).elim
          · -- (-93/128) * X + (-449/128) * Y + (45/2) < 0
            exact Or.inr (⟨by linarith, by linarith⟩)
    · intro p hp
      obtain ⟨X, Y, rfl⟩ := exists_rp hD7 p
      simp only [Set.mem_inter_iff, Set.mem_union, mem_halfR_rp hD7] at hp
      obtain ⟨⟨hpT, hY⟩, hdis⟩ := hp
      obtain ⟨hT0, hT1, hT2⟩ := rtri_ef_nonneg hD7 TGT_pos hpT
      unfold ef at hT0 hT1 hT2
      refine lexLE_rp hD7 (by linarith) (fun hYe => ?_)
      rcases hdis with h | ⟨c0, c1⟩ <;> linarith
  have hfree : ∀ ε : ℝ, 0 < ε → ∃ t s : ℝ, 0 < t ∧ t < ε ∧ 0 < s ∧ s < ε ∧
      rp 7 4 0 + t • (rp 7 1 0 + s • perp (rp 7 1 0)) ∈ unfilled D.toDissection ([i0, i1] : List (Fin N)).toFinset := by
    refine hfree_of hD7 (B := 3) (by norm_num) sr7_lt (τ := (1/4)) (by norm_num) _ _ _ ?_
    intro t ht htτ
    rw [pt_ccw_rp 7 hD7, hU]
    have ht2 : t ^ 2 ≤ (1/4) * t := by nlinarith [mul_le_mul_of_nonneg_left htτ ht.le]
    have ht2p : 0 < t ^ 2 := by positivity
    exact ⟨mem_rtri hD7 TGT_pos (by unfold ef; linarith) (by unfold ef; linarith) (by unfold ef; linarith), not_mem_rtri_of_edge1 hD7 T0_pos (by unfold ef; linarith), not_mem_rtri_of_edge0 hD7 T9_pos (by unfold ef; linarith)⟩
  have hblocked : ∃ δ : ℝ, 0 < δ ∧ ∀ t s : ℝ, 0 < t → t < δ → 0 < s → s < δ →
      rp 7 4 0 + t • (rp 7 1 0 - s • perp (rp 7 1 0)) ∉ unfilled D.toDissection ([i0, i1] : List (Fin N)).toFinset := by
    exact hblocked_base hD7 D.toDissection _ (fun p hp => hyT p (htarget ▸ hp)) 4
  obtain ⟨j, hj, k₀, k₁, k₂, hk01, hk02, hk12, hk₀, ⟨c', hc', hk₁⟩, hk₂⟩ :=
    placement_completeness D.toDissection ([i0, i1] : List (Fin N)).toFinset (rp 7 4 0) (rp 7 1 0) (rp_unit hD7 (by norm_num)) hlex hfree hblocked
  have hcong : (D.tile j).Congruent MODEL := (D.tiles_congruent j).trans hmodel
  obtain ⟨hMa, hMb, hMc⟩ := MODEL_sides
  have hj0 : j ≠ i0 := fun h => hj (by rw [h]; simp)
  have hj1 : j ≠ i1 := fun h => hj (by rw [h]; simp)
  rcases six_placements hcong hMa hMb hMc (rp_unit hD7 (by norm_num)) hk01 hk02 hk12 hk₀ hc' hk₁ hk₂ with
    ⟨hP, hQ⟩ | ⟨hP, hQ⟩ | ⟨hP, hQ⟩ | ⟨hP, hQ⟩ | ⟨hP, hQ⟩ | ⟨hP, hQ⟩
  · -- placement 1: (4, 16, 15)
    have hP' : (D.tile j).pts k₁ = rp 7 8 0 := by rw [hP, rp_add_smul]; norm_num
    have hQ' : (D.tile j).pts k₂ = rp 7 (79/8) (45/8) := by
      rw [hQ, placeThird_rp hD7 4 0 1 0 4 16 15 (47/8) (45/8) (by norm_num) (by norm_num) (by norm_num)]; norm_num
    have hjc : (D.tile j).carrier = T2.carrier :=
      carrier_eq_rtri_of_pts hD7 _ hk01 hk02 hk12 hk₀ hP' hQ' T2_pos
    exact node_7 D htarget hmodel i0 i1 j h0 h1 hjc
  · -- placement 2: (16, 4, 15)
    have hP' : (D.tile j).pts k₁ = rp 7 20 0 := by rw [hP, rp_add_smul]; norm_num
    have hQ' : (D.tile j).pts k₂ = rp 7 (175/32) (45/32) := by
      rw [hQ, placeThird_rp hD7 4 0 1 0 16 4 15 (47/32) (45/32) (by norm_num) (by norm_num) (by norm_num)]; norm_num
    exact (escape_of D.toDissection htarget j k₁ hP' (not_mem_rtri_of_edge1 hD7 TGT_pos (by unfold ef; norm_num)))
  · -- placement 3: (4, 15, 16)
    have hP' : (D.tile j).pts k₁ = rp 7 8 0 := by rw [hP, rp_add_smul]; norm_num
    have hQ' : (D.tile j).pts k₂ = rp 7 (17/8) (45/8) := by
      rw [hQ, placeThird_rp hD7 4 0 1 0 4 15 16 (-15/8) (45/8) (by norm_num) (by norm_num) (by norm_num)]; norm_num
    have hjc : (D.tile j).carrier = T8.carrier :=
      carrier_eq_rtri_of_pts hD7 _ hk01 hk02 hk12 hk₀ hP' hQ' T8_pos
    exact (overlap_of D.toDissection hj0.symm h0 hjc (w := rp 7 4 (3510/1457))
      (mem_interior_rtri hD7 T0_pos (by unfold ef; norm_num) (by unfold ef; norm_num) (by unfold ef; norm_num))
      (mem_interior_rtri hD7 T8_pos (by unfold ef; norm_num) (by unfold ef; norm_num) (by unfold ef; norm_num)))
  · -- placement 4: (15, 4, 16)
    have hP' : (D.tile j).pts k₁ = rp 7 19 0 := by rw [hP, rp_add_smul]; norm_num
    have hQ' : (D.tile j).pts k₂ = rp 7 (7/2) (3/2) := by
      rw [hQ, placeThird_rp hD7 4 0 1 0 15 4 16 (-1/2) (3/2) (by norm_num) (by norm_num) (by norm_num)]; norm_num
    exact (escape_of D.toDissection htarget j k₁ hP' (not_mem_rtri_of_edge1 hD7 TGT_pos (by unfold ef; norm_num)))
  · -- placement 5: (16, 15, 4)
    have hP' : (D.tile j).pts k₁ = rp 7 20 0 := by rw [hP, rp_add_smul]; norm_num
    have hQ' : (D.tile j).pts k₂ = rp 7 (593/32) (45/32) := by
      rw [hQ, placeThird_rp hD7 4 0 1 0 16 15 4 (465/32) (45/32) (by norm_num) (by norm_num) (by norm_num)]; norm_num
    exact (escape_of D.toDissection htarget j k₂ hQ' (not_mem_rtri_of_edge1 hD7 TGT_pos (by unfold ef; norm_num)))
  · -- placement 6: (15, 16, 4)
    have hP' : (D.tile j).pts k₁ = rp 7 19 0 := by rw [hP, rp_add_smul]; norm_num
    have hQ' : (D.tile j).pts k₂ = rp 7 (39/2) (3/2) := by
      rw [hQ, placeThird_rp hD7 4 0 1 0 15 16 4 (31/2) (3/2) (by norm_num) (by norm_num) (by norm_num)]; norm_num
    exact (escape_of D.toDissection htarget j k₂ hQ' (not_mem_rtri_of_edge1 hD7 TGT_pos (by unfold ef; norm_num)))

/-- Node 1: 1 placed tile(s), `v = (0, 0)`, `d = (47/128, 45/128·r)`; kills: escape(Q, edge 2), escape(Q, edge 2), escape(Q, edge 2), escape(Q, edge 2), child 2, child 6. -/
theorem node_1 {N : ℕ} (D : CongruentDissection N)
    (htarget : D.target.carrier = TGT.carrier) (hmodel : D.model.Congruent MODEL)
    (i0 : Fin N) (h0 : (D.tile i0).carrier = T0.carrier)
    : False := by
  classical
  have hyT : ∀ p ∈ TGT.carrier, 0 ≤ p 1 := fun p hp => target_y_nonneg hD7 (by norm_num) TGT_pos hp
  have hU : ∀ p, p ∈ unfilled D.toDissection ([i0] : List (Fin N)).toFinset ↔ p ∈ TGT.carrier ∧ p ∉ T0.carrier := by
    intro p; rw [mem_unfilled_iff, htarget]
    simp [h0]
  have hlex : ∀ p ∈ closure (unfilled D.toDissection ([i0] : List (Fin N)).toFinset), LexLE (rp 7 0 0) p := by
    refine hlex_of D.toDissection _ _ ((TGT.carrier ∩ halfR 7 0 1 0) ∩ (halfR 7 1 0 0)) ((TGT.isCompact.isClosed.inter (isClosed_halfR _ _ _ _)).inter (isClosed_halfR _ _ _ _)) ?_ ?_
    · intro p hpT hnot
      obtain ⟨X, Y, rfl⟩ := exists_rp hD7 p
      have hpT' : rp 7 X Y ∈ TGT.carrier := htarget ▸ hpT
      obtain ⟨hT0, hT1, hT2⟩ := rtri_ef_nonneg hD7 TGT_pos hpT'
      unfold ef at hT0 hT1 hT2
      have hn0 : ¬ (0 ≤ 0 * X + 4 * Y + 0 ∧ 0 ≤ (-45/8) * X + (15/8) * Y + (45/2) ∧ 0 ≤ (45/8) * X + (-47/8) * Y + 0) := fun h =>
        hnot i0 (by simp) (by rw [h0]; exact mem_rtri hD7 T0_pos (by unfold ef; linarith [h.1]) (by unfold ef; linarith [h.2.1]) (by unfold ef; linarith [h.2.2]))
      have hY : 0 ≤ Y := by
        by_contra hR; push_neg at hR
        linarith
      simp only [Set.mem_inter_iff, Set.mem_union, mem_halfR_rp hD7]
      refine ⟨⟨hpT', by linarith⟩, ?_⟩
      rcases le_or_gt 0 X with hX | hX
      · exact (by linarith)
      · -- the region X < xv, Y ≥ yv
        exfalso; linarith
    · intro p hp
      obtain ⟨X, Y, rfl⟩ := exists_rp hD7 p
      simp only [Set.mem_inter_iff, Set.mem_union, mem_halfR_rp hD7] at hp
      obtain ⟨⟨hpT, hY⟩, hdis⟩ := hp
      obtain ⟨hT0, hT1, hT2⟩ := rtri_ef_nonneg hD7 TGT_pos hpT
      unfold ef at hT0 hT1 hT2
      refine lexLE_rp hD7 (by linarith) (fun hYe => ?_)
      rcases hdis with h <;> linarith
  have hfree : ∀ ε : ℝ, 0 < ε → ∃ t s : ℝ, 0 < t ∧ t < ε ∧ 0 < s ∧ s < ε ∧
      rp 7 0 0 + t • (rp 7 (47/128) (45/128) + s • perp (rp 7 (47/128) (45/128))) ∈ unfilled D.toDissection ([i0] : List (Fin N)).toFinset := by
    refine hfree_of hD7 (B := 3) (by norm_num) sr7_lt (τ := (1/16)) (by norm_num) _ _ _ ?_
    intro t ht htτ
    rw [pt_ccw_rp 7 hD7, hU]
    have ht2 : t ^ 2 ≤ (1/16) * t := by nlinarith [mul_le_mul_of_nonneg_left htτ ht.le]
    have ht2p : 0 < t ^ 2 := by positivity
    exact ⟨mem_rtri hD7 TGT_pos (by unfold ef; linarith) (by unfold ef; linarith) (by unfold ef; linarith), not_mem_rtri_of_edge2 hD7 T0_pos (by unfold ef; linarith)⟩
  have hblocked : ∃ δ : ℝ, 0 < δ ∧ ∀ t s : ℝ, 0 < t → t < δ → 0 < s → s < δ →
      rp 7 0 0 + t • (rp 7 (47/128) (45/128) - s • perp (rp 7 (47/128) (45/128))) ∉ unfilled D.toDissection ([i0] : List (Fin N)).toFinset := by
    have hsub : T0.carrier ⊆ (D.tile i0).carrier := (h0.trans
      (carrier_eq_rtri_of_pts hD7 T0 (k₀ := 0) (k₁ := 1) (k₂ := 2) (by decide) (by decide) (by decide) rfl rfl rfl T0_pos)).symm.subset
    refine hblocked_of_wedge hD7 sr7_gt1 D.toDissection _ (i := i0) (by simp) _ _ T0 hsub rfl
      (wedge_interior T0 (rp 7 (47/128) (45/128)) (sr 7 • perp (rp 7 (47/128) (45/128))) 0 (1/16) (-32/45) (47/720) ?_ ?_ ?_ ?_)
    · rw [T0_pts.1, T0_pts.2.1, T0_pts.2.2]; refine plane_ext ?_ ?_ <;> simp <;> ring
    · rw [sr_smul_perp_rp hD7, T0_pts.1, T0_pts.2.1, T0_pts.2.2]; refine plane_ext ?_ ?_ <;> simp <;> ring
    · exact Or.inr ⟨by norm_num, by norm_num⟩
    · exact Or.inl (by norm_num)
  obtain ⟨j, hj, k₀, k₁, k₂, hk01, hk02, hk12, hk₀, ⟨c', hc', hk₁⟩, hk₂⟩ :=
    placement_completeness D.toDissection ([i0] : List (Fin N)).toFinset (rp 7 0 0) (rp 7 (47/128) (45/128)) (rp_unit hD7 (by norm_num)) hlex hfree hblocked
  have hcong : (D.tile j).Congruent MODEL := (D.tiles_congruent j).trans hmodel
  obtain ⟨hMa, hMb, hMc⟩ := MODEL_sides
  have hj0 : j ≠ i0 := fun h => hj (by rw [h]; simp)
  rcases six_placements hcong hMa hMb hMc (rp_unit hD7 (by norm_num)) hk01 hk02 hk12 hk₀ hc' hk₁ hk₂ with
    ⟨hP, hQ⟩ | ⟨hP, hQ⟩ | ⟨hP, hQ⟩ | ⟨hP, hQ⟩ | ⟨hP, hQ⟩ | ⟨hP, hQ⟩
  · -- placement 1: (4, 16, 15)
    have hP' : (D.tile j).pts k₁ = rp 7 (47/32) (45/32) := by rw [hP, rp_add_smul]; norm_num
    have hQ' : (D.tile j).pts k₂ = rp 7 (-5983/512) (2115/512) := by
      rw [hQ, placeThird_rp hD7 0 0 (47/128) (45/128) 4 16 15 (47/8) (45/8) (by norm_num) (by norm_num) (by norm_num)]; norm_num
    exact (escape_of D.toDissection htarget j k₂ hQ' (not_mem_rtri_of_edge2 hD7 TGT_pos (by unfold ef; norm_num)))
  · -- placement 2: (16, 4, 15)
    have hP' : (D.tile j).pts k₁ = rp 7 (47/8) (45/8) := by rw [hP, rp_add_smul]; norm_num
    have hQ' : (D.tile j).pts k₂ = rp 7 (-5983/2048) (2115/2048) := by
      rw [hQ, placeThird_rp hD7 0 0 (47/128) (45/128) 16 4 15 (47/32) (45/32) (by norm_num) (by norm_num) (by norm_num)]; norm_num
    exact (escape_of D.toDissection htarget j k₂ hQ' (not_mem_rtri_of_edge2 hD7 TGT_pos (by unfold ef; norm_num)))
  · -- placement 3: (4, 15, 16)
    have hP' : (D.tile j).pts k₁ = rp 7 (47/32) (45/32) := by rw [hP, rp_add_smul]; norm_num
    have hQ' : (D.tile j).pts k₂ = rp 7 (-465/32) (45/32) := by
      rw [hQ, placeThird_rp hD7 0 0 (47/128) (45/128) 4 15 16 (-15/8) (45/8) (by norm_num) (by norm_num) (by norm_num)]; norm_num
    exact (escape_of D.toDissection htarget j k₂ hQ' (not_mem_rtri_of_edge2 hD7 TGT_pos (by unfold ef; norm_num)))
  · -- placement 4: (15, 4, 16)
    have hP' : (D.tile j).pts k₁ = rp 7 (705/128) (675/128) := by rw [hP, rp_add_smul]; norm_num
    have hQ' : (D.tile j).pts k₂ = rp 7 (-31/8) (3/8) := by
      rw [hQ, placeThird_rp hD7 0 0 (47/128) (45/128) 15 4 16 (-1/2) (3/2) (by norm_num) (by norm_num) (by norm_num)]; norm_num
    exact (escape_of D.toDissection htarget j k₂ hQ' (not_mem_rtri_of_edge2 hD7 TGT_pos (by unfold ef; norm_num)))
  · -- placement 5: (16, 15, 4)
    have hP' : (D.tile j).pts k₁ = rp 7 (47/8) (45/8) := by rw [hP, rp_add_smul]; norm_num
    have hQ' : (D.tile j).pts k₂ = rp 7 (15/8) (45/8) := by
      rw [hQ, placeThird_rp hD7 0 0 (47/128) (45/128) 16 15 4 (465/32) (45/32) (by norm_num) (by norm_num) (by norm_num)]; norm_num
    have hjc : (D.tile j).carrier = T1.carrier :=
      carrier_eq_rtri_of_pts hD7 _ hk01 hk02 hk12 hk₀ hP' hQ' T1_pos
    exact node_2 D htarget hmodel i0 j h0 hjc
  · -- placement 6: (15, 16, 4)
    have hP' : (D.tile j).pts k₁ = rp 7 (705/128) (675/128) := by rw [hP, rp_add_smul]; norm_num
    have hQ' : (D.tile j).pts k₂ = rp 7 2 6 := by
      rw [hQ, placeThird_rp hD7 0 0 (47/128) (45/128) 15 16 4 (31/2) (3/2) (by norm_num) (by norm_num) (by norm_num)]; norm_num
    have hjc : (D.tile j).carrier = T9.carrier :=
      carrier_eq_rtri_of_pts hD7 _ hk01 hk02 hk12 hk₀ hP' hQ' T9_pos
    exact node_6 D htarget hmodel i0 j h0 hjc

/-- Node 0: 0 placed tile(s), `v = (0, 0)`, `d = (1, 0)`; kills: child 1, escape(P, edge 1), escape(Q, edge 2), escape(Q, edge 2), escape(P, edge 1), escape(Q, edge 1). -/
theorem node_0 {N : ℕ} (D : CongruentDissection N)
    (htarget : D.target.carrier = TGT.carrier) (hmodel : D.model.Congruent MODEL)
    : False := by
  classical
  have hyT : ∀ p ∈ TGT.carrier, 0 ≤ p 1 := fun p hp => target_y_nonneg hD7 (by norm_num) TGT_pos hp
  have hU : ∀ p, p ∈ unfilled D.toDissection ([] : List (Fin N)).toFinset ↔ p ∈ TGT.carrier := by
    intro p; rw [mem_unfilled_iff, htarget]
    simp []
  have hlex : ∀ p ∈ closure (unfilled D.toDissection ([] : List (Fin N)).toFinset), LexLE (rp 7 0 0) p := by
    refine hlex_of D.toDissection _ _ ((TGT.carrier ∩ halfR 7 0 1 0) ∩ (halfR 7 1 0 0)) ((TGT.isCompact.isClosed.inter (isClosed_halfR _ _ _ _)).inter (isClosed_halfR _ _ _ _)) ?_ ?_
    · intro p hpT hnot
      obtain ⟨X, Y, rfl⟩ := exists_rp hD7 p
      have hpT' : rp 7 X Y ∈ TGT.carrier := htarget ▸ hpT
      obtain ⟨hT0, hT1, hT2⟩ := rtri_ef_nonneg hD7 TGT_pos hpT'
      unfold ef at hT0 hT1 hT2
      have hY : 0 ≤ Y := by
        by_contra hR; push_neg at hR
        linarith
      simp only [Set.mem_inter_iff, Set.mem_union, mem_halfR_rp hD7]
      refine ⟨⟨hpT', by linarith⟩, ?_⟩
      rcases le_or_gt 0 X with hX | hX
      · exact (by linarith)
      · -- the region X < xv, Y ≥ yv
        exfalso; linarith
    · intro p hp
      obtain ⟨X, Y, rfl⟩ := exists_rp hD7 p
      simp only [Set.mem_inter_iff, Set.mem_union, mem_halfR_rp hD7] at hp
      obtain ⟨⟨hpT, hY⟩, hdis⟩ := hp
      obtain ⟨hT0, hT1, hT2⟩ := rtri_ef_nonneg hD7 TGT_pos hpT
      unfold ef at hT0 hT1 hT2
      refine lexLE_rp hD7 (by linarith) (fun hYe => ?_)
      rcases hdis with h <;> linarith
  have hfree : ∀ ε : ℝ, 0 < ε → ∃ t s : ℝ, 0 < t ∧ t < ε ∧ 0 < s ∧ s < ε ∧
      rp 7 0 0 + t • (rp 7 1 0 + s • perp (rp 7 1 0)) ∈ unfilled D.toDissection ([] : List (Fin N)).toFinset := by
    refine hfree_of hD7 (B := 3) (by norm_num) sr7_lt (τ := (1/4)) (by norm_num) _ _ _ ?_
    intro t ht htτ
    rw [pt_ccw_rp 7 hD7, hU]
    have ht2 : t ^ 2 ≤ (1/4) * t := by nlinarith [mul_le_mul_of_nonneg_left htτ ht.le]
    have ht2p : 0 < t ^ 2 := by positivity
    exact mem_rtri hD7 TGT_pos (by unfold ef; linarith) (by unfold ef; linarith) (by unfold ef; linarith)
  have hblocked : ∃ δ : ℝ, 0 < δ ∧ ∀ t s : ℝ, 0 < t → t < δ → 0 < s → s < δ →
      rp 7 0 0 + t • (rp 7 1 0 - s • perp (rp 7 1 0)) ∉ unfilled D.toDissection ([] : List (Fin N)).toFinset := by
    exact hblocked_base hD7 D.toDissection _ (fun p hp => hyT p (htarget ▸ hp)) 0
  obtain ⟨j, hj, k₀, k₁, k₂, hk01, hk02, hk12, hk₀, ⟨c', hc', hk₁⟩, hk₂⟩ :=
    placement_completeness D.toDissection ([] : List (Fin N)).toFinset (rp 7 0 0) (rp 7 1 0) (rp_unit hD7 (by norm_num)) hlex hfree hblocked
  have hcong : (D.tile j).Congruent MODEL := (D.tiles_congruent j).trans hmodel
  obtain ⟨hMa, hMb, hMc⟩ := MODEL_sides
  rcases six_placements hcong hMa hMb hMc (rp_unit hD7 (by norm_num)) hk01 hk02 hk12 hk₀ hc' hk₁ hk₂ with
    ⟨hP, hQ⟩ | ⟨hP, hQ⟩ | ⟨hP, hQ⟩ | ⟨hP, hQ⟩ | ⟨hP, hQ⟩ | ⟨hP, hQ⟩
  · -- placement 1: (4, 16, 15)
    have hP' : (D.tile j).pts k₁ = rp 7 4 0 := by rw [hP, rp_add_smul]; norm_num
    have hQ' : (D.tile j).pts k₂ = rp 7 (47/8) (45/8) := by
      rw [hQ, placeThird_rp hD7 0 0 1 0 4 16 15 (47/8) (45/8) (by norm_num) (by norm_num) (by norm_num)]; norm_num
    have hjc : (D.tile j).carrier = T0.carrier :=
      carrier_eq_rtri_of_pts hD7 _ hk01 hk02 hk12 hk₀ hP' hQ' T0_pos
    exact node_1 D htarget hmodel j hjc
  · -- placement 2: (16, 4, 15)
    have hP' : (D.tile j).pts k₁ = rp 7 16 0 := by rw [hP, rp_add_smul]; norm_num
    have hQ' : (D.tile j).pts k₂ = rp 7 (47/32) (45/32) := by
      rw [hQ, placeThird_rp hD7 0 0 1 0 16 4 15 (47/32) (45/32) (by norm_num) (by norm_num) (by norm_num)]; norm_num
    exact (escape_of D.toDissection htarget j k₁ hP' (not_mem_rtri_of_edge1 hD7 TGT_pos (by unfold ef; norm_num)))
  · -- placement 3: (4, 15, 16)
    have hP' : (D.tile j).pts k₁ = rp 7 4 0 := by rw [hP, rp_add_smul]; norm_num
    have hQ' : (D.tile j).pts k₂ = rp 7 (-15/8) (45/8) := by
      rw [hQ, placeThird_rp hD7 0 0 1 0 4 15 16 (-15/8) (45/8) (by norm_num) (by norm_num) (by norm_num)]; norm_num
    exact (escape_of D.toDissection htarget j k₂ hQ' (not_mem_rtri_of_edge2 hD7 TGT_pos (by unfold ef; norm_num)))
  · -- placement 4: (15, 4, 16)
    have hP' : (D.tile j).pts k₁ = rp 7 15 0 := by rw [hP, rp_add_smul]; norm_num
    have hQ' : (D.tile j).pts k₂ = rp 7 (-1/2) (3/2) := by
      rw [hQ, placeThird_rp hD7 0 0 1 0 15 4 16 (-1/2) (3/2) (by norm_num) (by norm_num) (by norm_num)]; norm_num
    exact (escape_of D.toDissection htarget j k₂ hQ' (not_mem_rtri_of_edge2 hD7 TGT_pos (by unfold ef; norm_num)))
  · -- placement 5: (16, 15, 4)
    have hP' : (D.tile j).pts k₁ = rp 7 16 0 := by rw [hP, rp_add_smul]; norm_num
    have hQ' : (D.tile j).pts k₂ = rp 7 (465/32) (45/32) := by
      rw [hQ, placeThird_rp hD7 0 0 1 0 16 15 4 (465/32) (45/32) (by norm_num) (by norm_num) (by norm_num)]; norm_num
    exact (escape_of D.toDissection htarget j k₁ hP' (not_mem_rtri_of_edge1 hD7 TGT_pos (by unfold ef; norm_num)))
  · -- placement 6: (15, 16, 4)
    have hP' : (D.tile j).pts k₁ = rp 7 15 0 := by rw [hP, rp_add_smul]; norm_num
    have hQ' : (D.tile j).pts k₂ = rp 7 (31/2) (3/2) := by
      rw [hQ, placeThird_rp hD7 0 0 1 0 15 16 4 (31/2) (3/2) (by norm_num) (by norm_num) (by norm_num)]; norm_num
    exact (escape_of D.toDissection htarget j k₂ hQ' (not_mem_rtri_of_edge1 hD7 TGT_pos (by unfold ef; norm_num)))

/-! ## Non-vacuity: every placed tile is congruent to the model and inside the target, and
every node's placed tiles have pairwise disjoint interiors -- the node hypotheses describe
genuine partial configurations, not empty ones. -/

theorem T0_sides : dist (T0.pts 0) (T0.pts 1) ^ 2 = 16 ∧ dist (T0.pts 1) (T0.pts 2) ^ 2 = 225 ∧
    dist (T0.pts 2) (T0.pts 0) ^ 2 = 256 := by
  rw [T0_pts.1, T0_pts.2.1, T0_pts.2.2, dist_rp_sq 7 hD7, dist_rp_sq 7 hD7, dist_rp_sq 7 hD7]; norm_num
theorem T0_inside : T0.carrier ⊆ TGT.carrier :=
  rtri_subset hD7 T0_pos _ (mem_rtri hD7 TGT_pos (by unfold ef; norm_num) (by unfold ef; norm_num) (by unfold ef; norm_num)) (mem_rtri hD7 TGT_pos (by unfold ef; norm_num) (by unfold ef; norm_num) (by unfold ef; norm_num)) (mem_rtri hD7 TGT_pos (by unfold ef; norm_num) (by unfold ef; norm_num) (by unfold ef; norm_num))

theorem T1_sides : dist (T1.pts 0) (T1.pts 1) ^ 2 = 256 ∧ dist (T1.pts 1) (T1.pts 2) ^ 2 = 16 ∧
    dist (T1.pts 2) (T1.pts 0) ^ 2 = 225 := by
  rw [T1_pts.1, T1_pts.2.1, T1_pts.2.2, dist_rp_sq 7 hD7, dist_rp_sq 7 hD7, dist_rp_sq 7 hD7]; norm_num
theorem T1_inside : T1.carrier ⊆ TGT.carrier :=
  rtri_subset hD7 T1_pos _ (mem_rtri hD7 TGT_pos (by unfold ef; norm_num) (by unfold ef; norm_num) (by unfold ef; norm_num)) (mem_rtri hD7 TGT_pos (by unfold ef; norm_num) (by unfold ef; norm_num) (by unfold ef; norm_num)) (mem_rtri hD7 TGT_pos (by unfold ef; norm_num) (by unfold ef; norm_num) (by unfold ef; norm_num))

theorem T2_sides : dist (T2.pts 0) (T2.pts 1) ^ 2 = 16 ∧ dist (T2.pts 1) (T2.pts 2) ^ 2 = 225 ∧
    dist (T2.pts 2) (T2.pts 0) ^ 2 = 256 := by
  rw [T2_pts.1, T2_pts.2.1, T2_pts.2.2, dist_rp_sq 7 hD7, dist_rp_sq 7 hD7, dist_rp_sq 7 hD7]; norm_num
theorem T2_inside : T2.carrier ⊆ TGT.carrier :=
  rtri_subset hD7 T2_pos _ (mem_rtri hD7 TGT_pos (by unfold ef; norm_num) (by unfold ef; norm_num) (by unfold ef; norm_num)) (mem_rtri hD7 TGT_pos (by unfold ef; norm_num) (by unfold ef; norm_num) (by unfold ef; norm_num)) (mem_rtri hD7 TGT_pos (by unfold ef; norm_num) (by unfold ef; norm_num) (by unfold ef; norm_num))

theorem T3_sides : dist (T3.pts 0) (T3.pts 1) ^ 2 = 256 ∧ dist (T3.pts 1) (T3.pts 2) ^ 2 = 16 ∧
    dist (T3.pts 2) (T3.pts 0) ^ 2 = 225 := by
  rw [T3_pts.1, T3_pts.2.1, T3_pts.2.2, dist_rp_sq 7 hD7, dist_rp_sq 7 hD7, dist_rp_sq 7 hD7]; norm_num
theorem T3_inside : T3.carrier ⊆ TGT.carrier :=
  rtri_subset hD7 T3_pos _ (mem_rtri hD7 TGT_pos (by unfold ef; norm_num) (by unfold ef; norm_num) (by unfold ef; norm_num)) (mem_rtri hD7 TGT_pos (by unfold ef; norm_num) (by unfold ef; norm_num) (by unfold ef; norm_num)) (mem_rtri hD7 TGT_pos (by unfold ef; norm_num) (by unfold ef; norm_num) (by unfold ef; norm_num))

theorem T5_sides : dist (T5.pts 0) (T5.pts 1) ^ 2 = 225 ∧ dist (T5.pts 1) (T5.pts 2) ^ 2 = 16 ∧
    dist (T5.pts 2) (T5.pts 0) ^ 2 = 256 := by
  rw [T5_pts.1, T5_pts.2.1, T5_pts.2.2, dist_rp_sq 7 hD7, dist_rp_sq 7 hD7, dist_rp_sq 7 hD7]; norm_num
theorem T5_inside : T5.carrier ⊆ TGT.carrier :=
  rtri_subset hD7 T5_pos _ (mem_rtri hD7 TGT_pos (by unfold ef; norm_num) (by unfold ef; norm_num) (by unfold ef; norm_num)) (mem_rtri hD7 TGT_pos (by unfold ef; norm_num) (by unfold ef; norm_num) (by unfold ef; norm_num)) (mem_rtri hD7 TGT_pos (by unfold ef; norm_num) (by unfold ef; norm_num) (by unfold ef; norm_num))

theorem T9_sides : dist (T9.pts 0) (T9.pts 1) ^ 2 = 225 ∧ dist (T9.pts 1) (T9.pts 2) ^ 2 = 16 ∧
    dist (T9.pts 2) (T9.pts 0) ^ 2 = 256 := by
  rw [T9_pts.1, T9_pts.2.1, T9_pts.2.2, dist_rp_sq 7 hD7, dist_rp_sq 7 hD7, dist_rp_sq 7 hD7]; norm_num
theorem T9_inside : T9.carrier ⊆ TGT.carrier :=
  rtri_subset hD7 T9_pos _ (mem_rtri hD7 TGT_pos (by unfold ef; norm_num) (by unfold ef; norm_num) (by unfold ef; norm_num)) (mem_rtri hD7 TGT_pos (by unfold ef; norm_num) (by unfold ef; norm_num) (by unfold ef; norm_num)) (mem_rtri hD7 TGT_pos (by unfold ef; norm_num) (by unfold ef; norm_num) (by unfold ef; norm_num))

theorem disj_T0_T1 : Disjoint (interior T0.carrier) (interior T1.carrier) := by
  refine disj_of_sep_edge hD7 T0 T1 0 0 (47/8) (45/8) (by norm_num) ?_ ?_
  · intro k; fin_cases k
    · exact ⟨0, 0, T0_pts.1, by unfold ef; norm_num⟩
    · exact ⟨4, 0, T0_pts.2.1, by unfold ef; norm_num⟩
    · exact ⟨(47/8), (45/8), T0_pts.2.2, by unfold ef; norm_num⟩
  · intro k; fin_cases k
    · exact ⟨0, 0, T1_pts.1, by unfold ef; norm_num⟩
    · exact ⟨(47/8), (45/8), T1_pts.2.1, by unfold ef; norm_num⟩
    · exact ⟨(15/8), (45/8), T1_pts.2.2, by unfold ef; norm_num⟩
theorem disj_T0_T2 : Disjoint (interior T0.carrier) (interior T2.carrier) := by
  refine disj_of_sep_edge hD7 T0 T2 (47/8) (45/8) 4 0 (by norm_num) ?_ ?_
  · intro k; fin_cases k
    · exact ⟨0, 0, T0_pts.1, by unfold ef; norm_num⟩
    · exact ⟨4, 0, T0_pts.2.1, by unfold ef; norm_num⟩
    · exact ⟨(47/8), (45/8), T0_pts.2.2, by unfold ef; norm_num⟩
  · intro k; fin_cases k
    · exact ⟨4, 0, T2_pts.1, by unfold ef; norm_num⟩
    · exact ⟨8, 0, T2_pts.2.1, by unfold ef; norm_num⟩
    · exact ⟨(79/8), (45/8), T2_pts.2.2, by unfold ef; norm_num⟩
theorem disj_T1_T2 : Disjoint (interior T1.carrier) (interior T2.carrier) := by
  refine disj_of_sep_edge hD7 T1 T2 (47/8) (45/8) 0 0 (by norm_num) ?_ ?_
  · intro k; fin_cases k
    · exact ⟨0, 0, T1_pts.1, by unfold ef; norm_num⟩
    · exact ⟨(47/8), (45/8), T1_pts.2.1, by unfold ef; norm_num⟩
    · exact ⟨(15/8), (45/8), T1_pts.2.2, by unfold ef; norm_num⟩
  · intro k; fin_cases k
    · exact ⟨4, 0, T2_pts.1, by unfold ef; norm_num⟩
    · exact ⟨8, 0, T2_pts.2.1, by unfold ef; norm_num⟩
    · exact ⟨(79/8), (45/8), T2_pts.2.2, by unfold ef; norm_num⟩
theorem disj_T0_T3 : Disjoint (interior T0.carrier) (interior T3.carrier) := by
  refine disj_of_sep_edge hD7 T0 T3 (47/8) (45/8) 4 0 (by norm_num) ?_ ?_
  · intro k; fin_cases k
    · exact ⟨0, 0, T0_pts.1, by unfold ef; norm_num⟩
    · exact ⟨4, 0, T0_pts.2.1, by unfold ef; norm_num⟩
    · exact ⟨(47/8), (45/8), T0_pts.2.2, by unfold ef; norm_num⟩
  · intro k; fin_cases k
    · exact ⟨4, 0, T3_pts.1, by unfold ef; norm_num⟩
    · exact ⟨(79/8), (45/8), T3_pts.2.1, by unfold ef; norm_num⟩
    · exact ⟨(47/8), (45/8), T3_pts.2.2, by unfold ef; norm_num⟩
theorem disj_T1_T3 : Disjoint (interior T1.carrier) (interior T3.carrier) := by
  refine disj_of_sep_edge hD7 T1 T3 (47/8) (45/8) 0 0 (by norm_num) ?_ ?_
  · intro k; fin_cases k
    · exact ⟨0, 0, T1_pts.1, by unfold ef; norm_num⟩
    · exact ⟨(47/8), (45/8), T1_pts.2.1, by unfold ef; norm_num⟩
    · exact ⟨(15/8), (45/8), T1_pts.2.2, by unfold ef; norm_num⟩
  · intro k; fin_cases k
    · exact ⟨4, 0, T3_pts.1, by unfold ef; norm_num⟩
    · exact ⟨(79/8), (45/8), T3_pts.2.1, by unfold ef; norm_num⟩
    · exact ⟨(47/8), (45/8), T3_pts.2.2, by unfold ef; norm_num⟩
theorem disj_T2_T3 : Disjoint (interior T2.carrier) (interior T3.carrier) := by
  refine disj_of_sep_edge hD7 T2 T3 4 0 (79/8) (45/8) (by norm_num) ?_ ?_
  · intro k; fin_cases k
    · exact ⟨4, 0, T2_pts.1, by unfold ef; norm_num⟩
    · exact ⟨8, 0, T2_pts.2.1, by unfold ef; norm_num⟩
    · exact ⟨(79/8), (45/8), T2_pts.2.2, by unfold ef; norm_num⟩
  · intro k; fin_cases k
    · exact ⟨4, 0, T3_pts.1, by unfold ef; norm_num⟩
    · exact ⟨(79/8), (45/8), T3_pts.2.1, by unfold ef; norm_num⟩
    · exact ⟨(47/8), (45/8), T3_pts.2.2, by unfold ef; norm_num⟩
theorem disj_T0_T5 : Disjoint (interior T0.carrier) (interior T5.carrier) := by
  refine disj_of_sep_edge hD7 T0 T5 (47/8) (45/8) 4 0 (by norm_num) ?_ ?_
  · intro k; fin_cases k
    · exact ⟨0, 0, T0_pts.1, by unfold ef; norm_num⟩
    · exact ⟨4, 0, T0_pts.2.1, by unfold ef; norm_num⟩
    · exact ⟨(47/8), (45/8), T0_pts.2.2, by unfold ef; norm_num⟩
  · intro k; fin_cases k
    · exact ⟨4, 0, T5_pts.1, by unfold ef; norm_num⟩
    · exact ⟨(1217/128), (675/128), T5_pts.2.1, by unfold ef; norm_num⟩
    · exact ⟨6, 6, T5_pts.2.2, by unfold ef; norm_num⟩
theorem disj_T1_T5 : Disjoint (interior T1.carrier) (interior T5.carrier) := by
  refine disj_of_sep_edge hD7 T1 T5 6 6 4 0 (by norm_num) ?_ ?_
  · intro k; fin_cases k
    · exact ⟨0, 0, T1_pts.1, by unfold ef; norm_num⟩
    · exact ⟨(47/8), (45/8), T1_pts.2.1, by unfold ef; norm_num⟩
    · exact ⟨(15/8), (45/8), T1_pts.2.2, by unfold ef; norm_num⟩
  · intro k; fin_cases k
    · exact ⟨4, 0, T5_pts.1, by unfold ef; norm_num⟩
    · exact ⟨(1217/128), (675/128), T5_pts.2.1, by unfold ef; norm_num⟩
    · exact ⟨6, 6, T5_pts.2.2, by unfold ef; norm_num⟩
theorem disj_T2_T5 : Disjoint (interior T2.carrier) (interior T5.carrier) := by
  refine disj_of_sep_edge hD7 T2 T5 4 0 (79/8) (45/8) (by norm_num) ?_ ?_
  · intro k; fin_cases k
    · exact ⟨4, 0, T2_pts.1, by unfold ef; norm_num⟩
    · exact ⟨8, 0, T2_pts.2.1, by unfold ef; norm_num⟩
    · exact ⟨(79/8), (45/8), T2_pts.2.2, by unfold ef; norm_num⟩
  · intro k; fin_cases k
    · exact ⟨4, 0, T5_pts.1, by unfold ef; norm_num⟩
    · exact ⟨(1217/128), (675/128), T5_pts.2.1, by unfold ef; norm_num⟩
    · exact ⟨6, 6, T5_pts.2.2, by unfold ef; norm_num⟩
theorem disj_T0_T9 : Disjoint (interior T0.carrier) (interior T9.carrier) := by
  refine disj_of_sep_edge hD7 T0 T9 0 0 (47/8) (45/8) (by norm_num) ?_ ?_
  · intro k; fin_cases k
    · exact ⟨0, 0, T0_pts.1, by unfold ef; norm_num⟩
    · exact ⟨4, 0, T0_pts.2.1, by unfold ef; norm_num⟩
    · exact ⟨(47/8), (45/8), T0_pts.2.2, by unfold ef; norm_num⟩
  · intro k; fin_cases k
    · exact ⟨0, 0, T9_pts.1, by unfold ef; norm_num⟩
    · exact ⟨(705/128), (675/128), T9_pts.2.1, by unfold ef; norm_num⟩
    · exact ⟨2, 6, T9_pts.2.2, by unfold ef; norm_num⟩
theorem disj_T9_T2 : Disjoint (interior T9.carrier) (interior T2.carrier) := by
  refine disj_of_sep_edge hD7 T9 T2 (705/128) (675/128) 0 0 (by norm_num) ?_ ?_
  · intro k; fin_cases k
    · exact ⟨0, 0, T9_pts.1, by unfold ef; norm_num⟩
    · exact ⟨(705/128), (675/128), T9_pts.2.1, by unfold ef; norm_num⟩
    · exact ⟨2, 6, T9_pts.2.2, by unfold ef; norm_num⟩
  · intro k; fin_cases k
    · exact ⟨4, 0, T2_pts.1, by unfold ef; norm_num⟩
    · exact ⟨8, 0, T2_pts.2.1, by unfold ef; norm_num⟩
    · exact ⟨(79/8), (45/8), T2_pts.2.2, by unfold ef; norm_num⟩
theorem disj_T9_T3 : Disjoint (interior T9.carrier) (interior T3.carrier) := by
  refine disj_of_sep_edge hD7 T9 T3 (705/128) (675/128) 0 0 (by norm_num) ?_ ?_
  · intro k; fin_cases k
    · exact ⟨0, 0, T9_pts.1, by unfold ef; norm_num⟩
    · exact ⟨(705/128), (675/128), T9_pts.2.1, by unfold ef; norm_num⟩
    · exact ⟨2, 6, T9_pts.2.2, by unfold ef; norm_num⟩
  · intro k; fin_cases k
    · exact ⟨4, 0, T3_pts.1, by unfold ef; norm_num⟩
    · exact ⟨(79/8), (45/8), T3_pts.2.1, by unfold ef; norm_num⟩
    · exact ⟨(47/8), (45/8), T3_pts.2.2, by unfold ef; norm_num⟩
theorem disj_T9_T5 : Disjoint (interior T9.carrier) (interior T5.carrier) := by
  refine disj_of_sep_edge hD7 T9 T5 6 6 4 0 (by norm_num) ?_ ?_
  · intro k; fin_cases k
    · exact ⟨0, 0, T9_pts.1, by unfold ef; norm_num⟩
    · exact ⟨(705/128), (675/128), T9_pts.2.1, by unfold ef; norm_num⟩
    · exact ⟨2, 6, T9_pts.2.2, by unfold ef; norm_num⟩
  · intro k; fin_cases k
    · exact ⟨4, 0, T5_pts.1, by unfold ef; norm_num⟩
    · exact ⟨(1217/128), (675/128), T5_pts.2.1, by unfold ef; norm_num⟩
    · exact ⟨6, 6, T5_pts.2.2, by unfold ef; norm_num⟩

theorem node_2_config :
    Disjoint (interior T0.carrier) (interior T1.carrier) :=
  disj_T0_T1

theorem node_3_config :
    Disjoint (interior T0.carrier) (interior T1.carrier) ∧
    Disjoint (interior T0.carrier) (interior T2.carrier) ∧
    Disjoint (interior T1.carrier) (interior T2.carrier) :=
  ⟨disj_T0_T1, disj_T0_T2, disj_T1_T2⟩

theorem node_4_config :
    Disjoint (interior T0.carrier) (interior T1.carrier) ∧
    Disjoint (interior T0.carrier) (interior T2.carrier) ∧
    Disjoint (interior T0.carrier) (interior T3.carrier) ∧
    Disjoint (interior T1.carrier) (interior T2.carrier) ∧
    Disjoint (interior T1.carrier) (interior T3.carrier) ∧
    Disjoint (interior T2.carrier) (interior T3.carrier) :=
  ⟨disj_T0_T1, disj_T0_T2, disj_T0_T3, disj_T1_T2, disj_T1_T3, disj_T2_T3⟩

theorem node_5_config :
    Disjoint (interior T0.carrier) (interior T1.carrier) ∧
    Disjoint (interior T0.carrier) (interior T2.carrier) ∧
    Disjoint (interior T0.carrier) (interior T5.carrier) ∧
    Disjoint (interior T1.carrier) (interior T2.carrier) ∧
    Disjoint (interior T1.carrier) (interior T5.carrier) ∧
    Disjoint (interior T2.carrier) (interior T5.carrier) :=
  ⟨disj_T0_T1, disj_T0_T2, disj_T0_T5, disj_T1_T2, disj_T1_T5, disj_T2_T5⟩

theorem node_6_config :
    Disjoint (interior T0.carrier) (interior T9.carrier) :=
  disj_T0_T9

theorem node_7_config :
    Disjoint (interior T0.carrier) (interior T9.carrier) ∧
    Disjoint (interior T0.carrier) (interior T2.carrier) ∧
    Disjoint (interior T9.carrier) (interior T2.carrier) :=
  ⟨disj_T0_T9, disj_T0_T2, disj_T9_T2⟩

theorem node_8_config :
    Disjoint (interior T0.carrier) (interior T9.carrier) ∧
    Disjoint (interior T0.carrier) (interior T2.carrier) ∧
    Disjoint (interior T0.carrier) (interior T3.carrier) ∧
    Disjoint (interior T9.carrier) (interior T2.carrier) ∧
    Disjoint (interior T9.carrier) (interior T3.carrier) ∧
    Disjoint (interior T2.carrier) (interior T3.carrier) :=
  ⟨disj_T0_T9, disj_T0_T2, disj_T0_T3, disj_T9_T2, disj_T9_T3, disj_T2_T3⟩

theorem node_9_config :
    Disjoint (interior T0.carrier) (interior T9.carrier) ∧
    Disjoint (interior T0.carrier) (interior T2.carrier) ∧
    Disjoint (interior T0.carrier) (interior T5.carrier) ∧
    Disjoint (interior T9.carrier) (interior T2.carrier) ∧
    Disjoint (interior T9.carrier) (interior T5.carrier) ∧
    Disjoint (interior T2.carrier) (interior T5.carrier) :=
  ⟨disj_T0_T9, disj_T0_T2, disj_T0_T5, disj_T9_T2, disj_T9_T5, disj_T2_T5⟩

end Erdos634.N15IsoA

#print axioms Erdos634.N15IsoA.node_0
