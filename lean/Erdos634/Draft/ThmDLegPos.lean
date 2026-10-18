import Erdos634.Draft.ThmDLegLen
import Erdos634.Draft.ThmDCount

/-!
# Theorem D', (b): the POSITIONED leg  

`LegPos D model A B t e s r` : the leg `(t, e, r)` runs along the segment `[A, B]` with the lower end of the edge of `t` at the parameter `s`:
each tile has two vertices `lineMap A B s`, `lineMap A B s'` (`s < s'`), the junction `st.p` is `lineMap A B s'`, and the oriented edge has
length `(s' - s) |AB|`.  `exists_chain_leg_pos` is `ThmDLegLen.exists_chain_leg_len` (a copy, generated mechanically) with this extra
conjunct, proved in the same chain induction (`claim`).  `side_leg_pos` = `ThmDCount.side_leg_gen` with it.
-/

namespace Erdos634.Draft.APrimeLegBuild

open Erdos634.Geometry Erdos634.Draft.APrimeSeat1 Erdos634.Draft.APrimeLeg

/-- the positioned leg: tile `t` with oriented edge `e` whose lower end is at the parameter `s` of `[A,B]`, then the steps -/
def LegPos {N : ℕ} (D : Dissection N) (model : Tri) (A B : Plane) : Fin N → OE → ℝ → List (LegStep N) → Prop
  | t, e, s, [] => ∃ j k : Fin 3, j ≠ k ∧ (D.tile t).pts j = AffineMap.lineMap A B s ∧
      (D.tile t).pts k = AffineMap.lineMap A B (1 : ℝ) ∧ s < 1 ∧
      Erdos634.Draft.ThmD.wlen model e = (1 - s) * dist A B
  | t, e, s, st :: r => ∃ (s' : ℝ) (j k : Fin 3), j ≠ k ∧ (D.tile t).pts j = AffineMap.lineMap A B s ∧
      (D.tile t).pts k = AffineMap.lineMap A B s' ∧ s < s' ∧ s' < 1 ∧ st.p = AffineMap.lineMap A B s' ∧
      Erdos634.Draft.ThmD.wlen model e = (s' - s) * dist A B ∧ LegPos D model A B st.t st.e s' r


theorem exists_chain_leg_pos {N : ℕ} (D : Dissection N) (model : Tri)
    (hcong : ∀ i, model.Congruent (D.tile i)) (α : ℝ) (hirr : Irrational (α / Real.pi)) (hα : 0 < α)
    (hA0 : cornerAngle (model.pts 1) (model.pts 0) (model.pts 2) = α)
    (hA1 : cornerAngle (model.pts 2) (model.pts 1) (model.pts 0) = Real.pi - 3 * α)
    (hA2 : cornerAngle (model.pts 0) (model.pts 2) (model.pts 1) = 2 * α) (i : Fin 3) :
    ∃ (t0 : Fin N) (e0 : OE) (r : List (LegStep N)), RealLeg D α t0 e0 r ∧
      (D.tile t0).localAngle (D.target.pts i) = angVal α e0.l ∧
      (D.tile (lastTile t0 r)).localAngle (D.target.pts (i + 1)) =
        angVal α ((legEdges e0 r).getLast (List.cons_ne_nil _ _)).r ∧
      (r = [] → ∃ k : Fin 3, dist ((D.tile t0).pts k) ((D.tile t0).pts (k + 1)) =
        dist (D.target.pts i) (D.target.pts (i + 1))) ∧
      ((legEdges e0 r).map (Erdos634.Draft.ThmD.wlen model)).sum =
        dist (D.target.pts i) (D.target.pts (i + 1)) ∧
      (∃ j k : Fin 3, j ≠ k ∧ (D.tile t0).pts j = D.target.pts i ∧
        (D.tile t0).pts k ∈ segment ℝ (D.target.pts i) (D.target.pts (i + 1)) ∧
        (D.tile t0).pts k ≠ D.target.pts i) ∧
      (∃ j k : Fin 3, j ≠ k ∧ (D.tile (lastTile t0 r)).pts j = D.target.pts (i + 1) ∧
        (D.tile (lastTile t0 r)).pts k ∈ segment ℝ (D.target.pts i) (D.target.pts (i + 1)) ∧
        (D.tile (lastTile t0 r)).pts k ≠ D.target.pts (i + 1)) ∧
      LegPos D model (D.target.pts i) (D.target.pts (i + 1)) t0 e0 0 r := by
  classical
  set A := D.target.pts i with hAdef
  set B := D.target.pts (i + 1) with hBdef
  have hi3 : ∀ j : Fin 3, j = i ∨ j = i + 1 ∨ j = i + 2 := fun j => fin3_cases i j
  have hAB : A ≠ B := D.target.indep.injective.ne (fin3_ne i)
  obtain ⟨part, hcov, hdisj, -⟩ := Dissection.side_partition D i
  obtain ⟨f, c, hf, hle, hfi, hfi1, hfi2⟩ := exists_supporting D.target i
  have hfA : f A = c := hfi
  have hfB : f B = c := hfi1
  have hfline : ∀ s : ℝ, f (AffineMap.lineMap A B s) = c := by
    intro s
    rw [AffineMap.lineMap_apply]
    simp [vsub_eq_sub, vadd_eq_add, map_add, map_smul, map_sub, hfA, hfB]
  have hinj : Function.Injective (fun s : ℝ => (AffineMap.lineMap A B s : Plane)) :=
    AffineMap.lineMap_injective ℝ hAB
  -- re-index the covering edges by `Fin n`
  obtain ⟨n, ee, hee_inj, hee_mem⟩ : ∃ (n : ℕ) (ee : Fin n → Fin N × Fin 3),
      Function.Injective ee ∧ (∀ x, x ∈ part ↔ ∃ m, ee m = x) := by
    refine ⟨part.card, fun m => ((part.equivFin.symm m : part) : Fin N × Fin 3), ?_, ?_⟩
    · intro m m' h
      exact part.equivFin.symm.injective (Subtype.ext h)
    · intro x
      constructor
      · intro hx
        exact ⟨part.equivFin ⟨x, hx⟩, by simp⟩
      · rintro ⟨m, rfl⟩
        exact (part.equivFin.symm m).2
  have hmem : ∀ m, ee m ∈ part := fun m => (hee_mem _).2 ⟨m, rfl⟩
  have hseg_sub : ∀ m, (D.tile (ee m).1).edge (ee m).2 ⊆ segment ℝ A B := by
    intro m y hy
    rw [← hcov]
    exact Set.mem_iUnion₂.mpr ⟨ee m, hmem m, hy⟩
  have hcov' : ∀ y ∈ segment ℝ A B, ∃ m, y ∈ (D.tile (ee m).1).edge (ee m).2 := by
    intro y hy
    rw [← hcov] at hy
    obtain ⟨e, he, hye⟩ := Set.mem_iUnion₂.mp hy
    obtain ⟨m, rfl⟩ := (hee_mem e).1 he
    exact ⟨m, hye⟩
  have hdisj' : ∀ m m', m ≠ m' →
      ((D.tile (ee m).1).edge (ee m).2 ∩ (D.tile (ee m').1).edge (ee m').2).Subsingleton :=
    fun m m' hne => hdisj _ (hmem m) _ (hmem m') (fun h => hne (hee_inj h))
  -- vertices as parameters
  have hvert : ∀ m, ∀ j : Fin 3, (j = (ee m).2 ∨ j = (ee m).2 + 1) →
      ∃ s ∈ Set.Icc (0 : ℝ) 1, (D.tile (ee m).1).pts j = AffineMap.lineMap A B s := by
    intro m j hj
    have hjedge : (D.tile (ee m).1).pts j ∈ (D.tile (ee m).1).edge (ee m).2 := by
      rcases hj with rfl | rfl
      · exact left_mem_segment ℝ _ _
      · exact right_mem_segment ℝ _ _
    have := hseg_sub m hjedge
    rw [segment_eq_image_lineMap] at this
    obtain ⟨s, hs, hseq⟩ := this
    exact ⟨s, hs, hseq.symm⟩
  choose a ha hav using fun m => hvert m (ee m).2 (Or.inl rfl)
  choose b hb hbv using fun m => hvert m ((ee m).2 + 1) (Or.inr rfl)
  have hk1 : ∀ k : Fin 3, k ≠ k + 1 := fin3_ne
  have hab : ∀ m, a m ≠ b m := by
    intro m h
    apply (D.tile (ee m).1).indep.injective.ne (hk1 (ee m).2)
    rw [hav m, hbv m, h]
  let lo : Fin n → ℝ := fun m => min (a m) (b m)
  let hi : Fin n → ℝ := fun m => max (a m) (b m)
  have hedge : ∀ m, (D.tile (ee m).1).edge (ee m).2 =
      (fun s : ℝ => (AffineMap.lineMap A B s : Plane)) '' Set.Icc (lo m) (hi m) := by
    intro m
    have h1 := image_segment (𝕜 := ℝ) (AffineMap.lineMap A B : ℝ →ᵃ[ℝ] Plane) (a m) (b m)
    rw [segment_eq_uIcc] at h1
    show segment ℝ ((D.tile (ee m).1).pts (ee m).2) ((D.tile (ee m).1).pts ((ee m).2 + 1)) = _
    rw [hav m, hbv m]
    exact h1.symm
  have hCover : IntervalChain.Cover 1 lo hi := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro m; exact min_lt_max.mpr (hab m)
    · intro m; exact le_min (ha m).1 (hb m).1
    · intro m; exact max_le (ha m).2 (hb m).2
    · intro x hx0 hx1
      have hxs : (AffineMap.lineMap A B x : Plane) ∈ segment ℝ A B := by
        rw [segment_eq_image_lineMap]; exact ⟨x, ⟨hx0, hx1⟩, rfl⟩
      obtain ⟨m, hm⟩ := hcov' _ hxs
      rw [hedge m] at hm
      obtain ⟨y, hy, hyx⟩ := hm
      have : y = x := hinj hyx
      exact ⟨m, this ▸ hy⟩
    · intro m m' hne x y hx hx' hy hy'
      have hxm : (AffineMap.lineMap A B x : Plane) ∈ (D.tile (ee m).1).edge (ee m).2 := by
        rw [hedge m]; exact ⟨x, hx, rfl⟩
      have hxm' : (AffineMap.lineMap A B x : Plane) ∈ (D.tile (ee m').1).edge (ee m').2 := by
        rw [hedge m']; exact ⟨x, hx', rfl⟩
      have hym : (AffineMap.lineMap A B y : Plane) ∈ (D.tile (ee m).1).edge (ee m).2 := by
        rw [hedge m]; exact ⟨y, hy, rfl⟩
      have hym' : (AffineMap.lineMap A B y : Plane) ∈ (D.tile (ee m').1).edge (ee m').2 := by
        rw [hedge m']; exact ⟨y, hy', rfl⟩
      exact hinj (hdisj' m m' hne ⟨hxm, hxm'⟩ ⟨hym, hym'⟩)
  have hjk : ∀ m, ∃ j k : Fin 3, j ≠ k ∧ (D.tile (ee m).1).pts j = AffineMap.lineMap A B (lo m) ∧
      (D.tile (ee m).1).pts k = AffineMap.lineMap A B (hi m) := by
    intro m
    rcases lt_or_gt_of_ne (hab m) with h | h
    · exact ⟨(ee m).2, (ee m).2 + 1, hk1 _, by rw [hav m]; exact congrArg _ (min_eq_left h.le).symm,
        by rw [hbv m]; exact congrArg _ (max_eq_right h.le).symm⟩
    · exact ⟨(ee m).2 + 1, (ee m).2, (hk1 _).symm, by rw [hbv m]; exact congrArg _ (min_eq_right h.le).symm,
        by rw [hav m]; exact congrArg _ (max_eq_left h.le).symm⟩
  -- oriented edges
  have hoe : ∀ m, ∃ o : OE,
      (D.tile (ee m).1).localAngle (AffineMap.lineMap A B (lo m)) = angVal α o.l ∧
      (D.tile (ee m).1).localAngle (AffineMap.lineMap A B (hi m)) = angVal α o.r ∧
      Erdos634.Draft.ThmD.wlen model o = (hi m - lo m) * dist A B := by
    intro m
    rcases lt_or_gt_of_ne (hab m) with h | h
    · obtain ⟨o, ho1, ho2⟩ := exists_OE model _ (hcong (ee m).1) α hirr hA0 hA1 hA2 (ee m).2
      refine ⟨o, ?_, ?_, ?_⟩
      · show (D.tile (ee m).1).localAngle (AffineMap.lineMap A B (min (a m) (b m))) = _
        rw [min_eq_left h.le, ← hav m]; exact ho1
      · show (D.tile (ee m).1).localAngle (AffineMap.lineMap A B (max (a m) (b m))) = _
        rw [max_eq_right h.le, ← hbv m]; exact ho2
      · have hl := Erdos634.Draft.ThmD.edge_len_eq_fwd model _ (hcong (ee m).1) α hirr hα hA0 hA1 hA2
          (ee m).2 o ho1 ho2
        rw [hav m, hbv m, dist_lineMap_lineMap, Real.dist_eq] at hl
        show Erdos634.Draft.ThmD.wlen model o = (max (a m) (b m) - min (a m) (b m)) * dist A B
        rw [← hl, min_eq_left h.le, max_eq_right h.le, abs_of_nonpos (by linarith)]
        ring
    · obtain ⟨o, ho1, ho2⟩ := exists_OE_rev model _ (hcong (ee m).1) α hirr hA0 hA1 hA2 (ee m).2
      refine ⟨o, ?_, ?_, ?_⟩
      · show (D.tile (ee m).1).localAngle (AffineMap.lineMap A B (min (a m) (b m))) = _
        rw [min_eq_right h.le, ← hbv m]; exact ho1
      · show (D.tile (ee m).1).localAngle (AffineMap.lineMap A B (max (a m) (b m))) = _
        rw [max_eq_left h.le, ← hav m]; exact ho2
      · have hl := Erdos634.Draft.ThmD.edge_len_eq_rev model _ (hcong (ee m).1) α hirr hα hA0 hA1 hA2
          (ee m).2 o ho1 ho2
        rw [hav m, hbv m, dist_lineMap_lineMap, Real.dist_eq] at hl
        show Erdos634.Draft.ThmD.wlen model o = (max (a m) (b m) - min (a m) (b m)) * dist A B
        rw [← hl, min_eq_right h.le, max_eq_left h.le, abs_of_nonneg (by linarith)]
  choose oe hoe1 hoe2 hlen using hoe
  -- junction facts
  have hjunc : ∀ m m', hi m = lo m' →
      (AffineMap.lineMap A B (hi m) : Plane) ∈ frontier D.target.carrier ∧
      (AffineMap.lineMap A B (hi m) : Plane) ∉ Set.range D.target.pts ∧
      (ee m).1 ≠ (ee m').1 := by
    intro m m' hm
    have hpos : 0 < hi m := lt_of_le_of_lt (hCover.nonneg m) (hCover.lt m)
    have hlt1 : hi m < 1 := by rw [hm]; exact lt_of_lt_of_le (hCover.lt m') (hCover.le m')
    have hmm : m ≠ m' := by
      rintro rfl
      exact absurd hm (ne_of_gt (hCover.lt m))
    refine ⟨?_, ?_, ?_⟩
    · have hps : (AffineMap.lineMap A B (hi m) : Plane) ∈ D.target.edge i := by
        show _ ∈ segment ℝ (D.target.pts i) (D.target.pts (i + 1))
        rw [segment_eq_image_lineMap]
        exact ⟨hi m, ⟨hpos.le, hlt1.le⟩, rfl⟩
      exact Erdos634.SideWall.edge_subset_frontier D.target i hps
    · rintro ⟨j, hj⟩
      rcases hi3 j with hj0 | hj0 | hj0
      · have h0 : (AffineMap.lineMap A B (0:ℝ) : Plane) = D.target.pts j := by
          rw [hj0]; simp [hAdef]
        have := hinj (show (AffineMap.lineMap A B (hi m) : Plane) = AffineMap.lineMap A B 0 from
          hj.symm.trans h0.symm)
        exact absurd this (ne_of_gt hpos)
      · have h0 : (AffineMap.lineMap A B (1:ℝ) : Plane) = D.target.pts j := by
          rw [hj0]; simp [hBdef]
        have := hinj (show (AffineMap.lineMap A B (hi m) : Plane) = AffineMap.lineMap A B 1 from
          hj.symm.trans h0.symm)
        exact absurd this (ne_of_lt hlt1)
      · have := hfline (hi m)
        rw [← hj, hj0] at this
        linarith
    · intro htile
      apply hmm
      by_contra hne
      have hne2 : (ee m).2 ≠ (ee m').2 := by
        intro h2
        exact hne (hee_inj (Prod.ext htile h2))
      refine not_two_edges_on_line (D.tile (ee m).1) A B (ee m).2 (ee m').2 hne2
        (fun j hj => ?_) (fun j hj => ?_)
      · obtain ⟨s, -, hs⟩ := hvert m j hj; exact ⟨s, hs⟩
      · obtain ⟨s, -, hs⟩ := hvert m' j hj
        exact ⟨s, by rw [htile]; exact hs⟩
  have hhi_lt : ∀ m m', hi m = lo m' → hi m < 1 := by
    intro m m' hm
    rw [hm]; exact lt_of_lt_of_le (hCover.lt m') (hCover.le m')
  -- the chain
  obtain ⟨i0, hi0⟩ := IntervalChain.first_starts_at_zero hCover (by norm_num)
  obtain ⟨r0, hr0⟩ := chain_exists hCover i0
  have claim : ∀ (r : List (Fin n)) (m : Fin n), Chain lo hi m r →
      ∃ L : List (LegStep N), RealLeg D α (ee m).1 (oe m) L ∧
        ((legEdges (oe m) L).map (Erdos634.Draft.ThmD.wlen model)).sum = (1 - lo m) * dist A B ∧
        LegPos D model A B (ee m).1 (oe m) (lo m) L ∧
        (L = [] → r = []) ∧ ∃ z : Fin n,
        hi z = 1 ∧ lastTile (ee m).1 L = (ee z).1 ∧
        (legEdges (oe m) L).getLast (List.cons_ne_nil _ _) = oe z := by
    intro r
    induction r with
    | nil =>
      intro m hm
      have hm' : hi m = 1 := hm
      refine ⟨[], trivial, ?_, ?_, fun _ => rfl, m, hm, rfl, rfl⟩
      · simp only [legEdges, List.map_nil, List.map_cons, List.sum_cons, List.sum_nil, add_zero]
        rw [hlen m, hm']
      · obtain ⟨j, k, hjk', hj, hk⟩ := hjk m
        refine ⟨j, k, hjk', hj, by rw [hk, hm'], ?_, by rw [hlen m, hm']⟩
        have := hCover.lt m
        rw [hm'] at this
        exact this
    | cons m' r ih =>
      intro m hm
      obtain ⟨hmm', hrest⟩ := hm
      obtain ⟨L', hL', hsum', hpos', -, z, hz1, hz2, hz3⟩ := ih m' hrest
      obtain ⟨hfr, hnv, hne⟩ := hjunc m m' hmm'
      refine ⟨⟨AffineMap.lineMap A B (hi m), (ee m').1, oe m'⟩ :: L', ?_, ?_, ?_,
        fun h => absurd h (List.cons_ne_nil _ _), z, hz1, ?_, ?_⟩
      · refine ⟨hfr, hnv, hne, hoe2 m, ?_, hL'⟩
        show (D.tile (ee m').1).localAngle (AffineMap.lineMap A B (hi m)) = angVal α (oe m').l
        rw [hmm']; exact hoe1 m'
      · have e1 : legEdges (oe m) (⟨AffineMap.lineMap A B (hi m), (ee m').1, oe m'⟩ :: L') =
            oe m :: legEdges (oe m') L' := by simp [legEdges]
        rw [e1, List.map_cons, List.sum_cons, hsum', hlen m, hmm']
        ring
      · obtain ⟨j, k, hjk', hj, hk⟩ := hjk m
        refine ⟨hi m, j, k, hjk', hj, hk, hCover.lt m, hhi_lt m m' hmm', rfl, hlen m, ?_⟩
        rw [hmm']; exact hpos'
      · exact hz2
      · rw [getLast_legEdges_cons]; exact hz3
  obtain ⟨L, hL, hLs, hLpos, hLr, z, hz1, hz2, hz3⟩ := claim r0 i0 hr0
  have hseg : ∀ s ∈ Set.Icc (0 : ℝ) 1, (AffineMap.lineMap A B s : Plane) ∈ segment ℝ A B := by
    intro s hs
    rw [segment_eq_image_lineMap]; exact ⟨s, hs, rfl⟩
  have hfirstOn : ∃ j k : Fin 3, j ≠ k ∧ (D.tile (ee i0).1).pts j = A ∧
      (D.tile (ee i0).1).pts k ∈ segment ℝ A B ∧ (D.tile (ee i0).1).pts k ≠ A := by
    have h0 : lo i0 = 0 := hi0
    have hlt := hCover.lt i0
    rcases le_total (a i0) (b i0) with h | h
    · have ha0 : a i0 = 0 := by
        have : lo i0 = a i0 := min_eq_left h
        linarith
      have hb0 : 0 < b i0 := by
        have : hi i0 = b i0 := max_eq_right h
        linarith
      refine ⟨(ee i0).2, (ee i0).2 + 1, hk1 _, ?_, ?_, ?_⟩
      · rw [hav i0, ha0, AffineMap.lineMap_apply_zero]
      · rw [hbv i0]; exact hseg _ ⟨hb0.le, (hb i0).2⟩
      · rw [hbv i0]
        intro heq
        have : b i0 = 0 := by
          apply hinj
          simp only
          rw [heq]; simp
        linarith
    · have hb0 : b i0 = 0 := by
        have : lo i0 = b i0 := min_eq_right h
        linarith
      have ha0 : 0 < a i0 := by
        have : hi i0 = a i0 := max_eq_left h
        linarith
      refine ⟨(ee i0).2 + 1, (ee i0).2, (hk1 _).symm, ?_, ?_, ?_⟩
      · rw [hbv i0, hb0, AffineMap.lineMap_apply_zero]
      · rw [hav i0]; exact hseg _ ⟨ha0.le, (ha i0).2⟩
      · rw [hav i0]
        intro heq
        have : a i0 = 0 := by
          apply hinj
          simp only
          rw [heq]; simp
        linarith
  have hlastOn : ∃ j k : Fin 3, j ≠ k ∧ (D.tile (ee z).1).pts j = B ∧
      (D.tile (ee z).1).pts k ∈ segment ℝ A B ∧ (D.tile (ee z).1).pts k ≠ B := by
    have hlt := hCover.lt z
    rcases le_total (a z) (b z) with h | h
    · have hb1 : b z = 1 := by
        have : hi z = b z := max_eq_right h
        linarith
      have ha1 : a z < 1 := by
        have : lo z = a z := min_eq_left h
        linarith
      refine ⟨(ee z).2 + 1, (ee z).2, (hk1 _).symm, ?_, ?_, ?_⟩
      · rw [hbv z, hb1, AffineMap.lineMap_apply_one]
      · rw [hav z]; exact hseg _ ⟨(ha z).1, (ha z).2⟩
      · rw [hav z]
        intro heq
        have : a z = 1 := by
          apply hinj
          simp only
          rw [heq]; simp
        linarith
    · have ha1 : a z = 1 := by
        have : hi z = a z := max_eq_left h
        linarith
      have hb1 : b z < 1 := by
        have : lo z = b z := min_eq_right h
        linarith
      refine ⟨(ee z).2, (ee z).2 + 1, hk1 _, ?_, ?_, ?_⟩
      · rw [hav z, ha1, AffineMap.lineMap_apply_one]
      · rw [hbv z]; exact hseg _ ⟨(hb z).1, (hb z).2⟩
      · rw [hbv z]
        intro heq
        have : b z = 1 := by
          apply hinj
          simp only
          rw [heq]; simp
        linarith
  refine ⟨(ee i0).1, oe i0, L, hL, ?_, ?_, ?_, ?_, hfirstOn, ?_, ?_⟩
  · have := hoe1 i0
    have h0 : lo i0 = 0 := hi0
    rw [h0] at this
    simpa using this
  · rw [hz2, hz3]
    have := hoe2 z
    rw [hz1] at this
    simpa using this
  · intro hL0
    have hr00 : r0 = [] := hLr hL0
    subst hr00
    have hhi : hi i0 = 1 := hr0
    have hlo : lo i0 = 0 := hi0
    refine ⟨(ee i0).2, ?_⟩
    rw [hav i0, hbv i0, dist_lineMap_lineMap]
    have hd : dist (a i0) (b i0) = 1 := by
      rw [Real.dist_eq]
      rcases le_total (a i0) (b i0) with h | h
      · have h1 : lo i0 = a i0 := min_eq_left h
        have h2 : hi i0 = b i0 := max_eq_right h
        rw [abs_of_nonpos (by linarith)]; linarith
      · have h1 : lo i0 = b i0 := min_eq_right h
        have h2 : hi i0 = a i0 := max_eq_left h
        rw [abs_of_nonneg (by linarith)]; linarith
    rw [hd, one_mul]
  · rw [hLs]
    have h0 : lo i0 = 0 := hi0
    rw [h0]
    ring
  · rw [hz2]; exact hlastOn
  · have h0 : lo i0 = 0 := hi0
    rw [h0] at hLpos
    exact hLpos


end Erdos634.Draft.APrimeLegBuild

#print axioms Erdos634.Draft.APrimeLegBuild.exists_chain_leg_len
