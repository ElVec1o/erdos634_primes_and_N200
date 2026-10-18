import Erdos634.Draft.APrimeLeg
import Erdos634.SideWall
import Erdos634.TileAt
import Erdos634.IntervalChain
import Erdos634.EdgeChain
import Erdos634.VertexFigureReal

/-!
# APRIME: building a `RealLeg` from a target side, and the corner hypotheses  

Discharges items (i)-(iii) named as remaining in `Draft/APrimeLeg.lean`.

* `exists_chain_leg` -- **construction.**  For any `Dissection D` whose tiles are congruent to a model
  with corner angles `α, π − 3α, 2α` (`α/π` irrational) and any side `i` of the target, there is a
  `RealLeg` (tile `t0`, oriented edge `e0`, steps `r`) running along the side from `pts i` to `pts (i+1)`:
  the first tile has its `e0.l`-angle at `pts i`, the last tile its last `.r`-angle at `pts (i+1)`.
  Route: `Dissection.side_partition` (a finite exactly-once edge cover of the side), edge endpoints
  parametrised by `lineMap A B`, `IntervalChain.successor`/`first_starts_at_zero` order the edges,
  consecutive edges meet at a point of the open side (a frontier non-vertex of the target),
  distinct edges of one tile cannot both lie on a line (`AffineIndependent` in dimension one).
* `corner_first` / `corner_last` -- the first/last angle hypotheses of `RealLeg.counting_identity`
  from the target corner (`∑ tiles = corner angle`, only `α, β, γ` occur, `cnt_eq`).
  Corner angle `α` forces the tile angle `α`; corner angle `α`, `π − 3α` or `π − 2α` excludes `γ`.
* `side_leg_counting` -- both together with `RealLeg.counting_identity`.
-/

namespace Erdos634.Draft.APrimeLegBuild

open Erdos634.Geometry Erdos634.Draft.APrimeSeat1 Erdos634.Draft.APrimeLeg

/-! ### 1. Chains of intervals -/

/-- A chain of intervals from `i` to the right end `1`. -/
def Chain {n : ℕ} (lo hi : Fin n → ℝ) : Fin n → List (Fin n) → Prop
  | i, [] => hi i = 1
  | i, j :: r => hi i = lo j ∧ Chain lo hi j r

theorem chain_exists {n : ℕ} {lo hi : Fin n → ℝ} (H : IntervalChain.Cover 1 lo hi) :
    ∀ i, ∃ r, Chain lo hi i r := by
  classical
  have key : ∀ k : ℕ, ∀ i : Fin n,
      (Finset.univ.filter (fun j => lo i < lo j)).card = k → ∃ r, Chain lo hi i r := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro i hk
      by_cases h1 : hi i = 1
      · exact ⟨[], h1⟩
      · have hlt : hi i < 1 := lt_of_le_of_ne (H.le i) h1
        obtain ⟨j, hj⟩ := IntervalChain.successor H i hlt
        have hij : lo i < lo j := by rw [hj]; exact H.lt i
        have hsub : (Finset.univ.filter (fun j' => lo j < lo j')) ⊂
            (Finset.univ.filter (fun j' => lo i < lo j')) := by
          refine (Finset.ssubset_iff_of_subset ?_).mpr ⟨j, ?_, ?_⟩
          · intro x hx
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
            exact lt_trans hij hx
          · simp [hij]
          · simp
        obtain ⟨r, hr⟩ := ih (Finset.univ.filter (fun j' => lo j < lo j')).card
          (by rw [← hk]; exact Finset.card_lt_card hsub) j rfl
        exact ⟨j :: r, hj.symm, hr⟩
  exact fun i => key _ i rfl

/-! ### 2. The last tile, the last edge -/

/-- The tile at the end of a leg. -/
def lastTile {N : ℕ} : Fin N → List (LegStep N) → Fin N
  | t, [] => t
  | _, s :: r => lastTile s.t r

theorem getLast_legEdges_cons {N : ℕ} (e : OE) (s : LegStep N) (L : List (LegStep N)) :
    (legEdges e (s :: L)).getLast (List.cons_ne_nil _ _) =
      (legEdges s.e L).getLast (List.cons_ne_nil _ _) := by
  simp [legEdges]

/-! ### 3. The oriented edge of a tile edge, both directions -/

theorem exists_OE_rev (model T : Tri) (hc : model.Congruent T) (α : ℝ)
    (hirr : Irrational (α / Real.pi))
    (hA0 : cornerAngle (model.pts 1) (model.pts 0) (model.pts 2) = α)
    (hA1 : cornerAngle (model.pts 2) (model.pts 1) (model.pts 0) = Real.pi - 3 * α)
    (hA2 : cornerAngle (model.pts 0) (model.pts 2) (model.pts 1) = 2 * α) (k : Fin 3) :
    ∃ e : OE, T.localAngle (T.pts (k + 1)) = angVal α e.l ∧ T.localAngle (T.pts k) = angVal α e.r := by
  obtain ⟨a0, h0⟩ := corner_ang model T hc α hA0 hA1 hA2 k
  obtain ⟨a1, h1⟩ := corner_ang model T hc α hA0 hA1 hA2 (k + 1)
  obtain ⟨a2, h2⟩ := corner_ang model T hc α hA0 hA1 hA2 (k + 2)
  have hsum : angVal α a0 + angVal α a1 + angVal α a2 = Real.pi := by
    rw [← h0, ← h1, ← h2]
    have hs := cornerAngle_sum T
    fin_cases k <;> simp <;> linarith
  have hd := three_angles_distinct α hirr a0 a1 a2 hsum
  obtain ⟨e, hl, hr⟩ := exists_OE_of_ne a1 a0 hd.1.symm
  refine ⟨e, ?_, ?_⟩
  · rw [Tri.localAngle_vertex, h1, hl]
  · rw [Tri.localAngle_vertex, h0, hr]

/-! ### 4. Two edges of one tile cannot lie on a line -/

theorem not_two_edges_on_line (T : Tri) (A B : Plane) (k k' : Fin 3) (hkk : k ≠ k')
    (h1 : ∀ j : Fin 3, (j = k ∨ j = k + 1) → ∃ s : ℝ, T.pts j = AffineMap.lineMap A B s)
    (h2 : ∀ j : Fin 3, (j = k' ∨ j = k' + 1) → ∃ s : ℝ, T.pts j = AffineMap.lineMap A B s) :
    False := by
  have hcov : ∀ j : Fin 3, ∃ s : ℝ, T.pts j = AffineMap.lineMap A B s := by
    have hall : ∀ k k' : Fin 3, k ≠ k' → ∀ j : Fin 3, (j = k ∨ j = k + 1) ∨ (j = k' ∨ j = k' + 1) := by
      decide
    intro j
    rcases hall k k' hkk j with h | h
    · exact h1 j h
    · exact h2 j h
  choose s hs using hcov
  have hfun : T.pts = (AffineMap.lineMap A B : ℝ →ᵃ[ℝ] Plane) ∘ s := by
    funext j; exact hs j
  have hind : AffineIndependent ℝ ((AffineMap.lineMap A B : ℝ →ᵃ[ℝ] Plane) ∘ s) := by
    rw [← hfun]; exact T.indep
  have hs' : AffineIndependent ℝ s := hind.of_comp _
  have := hs'.card_le_finrank_succ
  have h2 := Submodule.finrank_le (vectorSpan ℝ (Set.range s))
  simp at this h2
  omega

/-! ### 5. The construction -/

theorem fin3_cases (i j : Fin 3) : j = i ∨ j = i + 1 ∨ j = i + 2 := by
  revert i j; decide

theorem fin3_ne (i : Fin 3) : i ≠ i + 1 := by
  revert i; decide

theorem exists_chain_leg {N : ℕ} (D : Dissection N) (model : Tri)
    (hcong : ∀ i, model.Congruent (D.tile i)) (α : ℝ) (hirr : Irrational (α / Real.pi))
    (hA0 : cornerAngle (model.pts 1) (model.pts 0) (model.pts 2) = α)
    (hA1 : cornerAngle (model.pts 2) (model.pts 1) (model.pts 0) = Real.pi - 3 * α)
    (hA2 : cornerAngle (model.pts 0) (model.pts 2) (model.pts 1) = 2 * α) (i : Fin 3) :
    ∃ (t0 : Fin N) (e0 : OE) (r : List (LegStep N)), RealLeg D α t0 e0 r ∧
      (D.tile t0).localAngle (D.target.pts i) = angVal α e0.l ∧
      (D.tile (lastTile t0 r)).localAngle (D.target.pts (i + 1)) =
        angVal α ((legEdges e0 r).getLast (List.cons_ne_nil _ _)).r ∧
      (r = [] → ∃ k : Fin 3, dist ((D.tile t0).pts k) ((D.tile t0).pts (k + 1)) =
        dist (D.target.pts i) (D.target.pts (i + 1))) := by
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
  -- oriented edges
  have hoe : ∀ m, ∃ o : OE,
      (D.tile (ee m).1).localAngle (AffineMap.lineMap A B (lo m)) = angVal α o.l ∧
      (D.tile (ee m).1).localAngle (AffineMap.lineMap A B (hi m)) = angVal α o.r := by
    intro m
    rcases lt_or_gt_of_ne (hab m) with h | h
    · obtain ⟨o, ho1, ho2⟩ := exists_OE model _ (hcong (ee m).1) α hirr hA0 hA1 hA2 (ee m).2
      refine ⟨o, ?_, ?_⟩
      · show (D.tile (ee m).1).localAngle (AffineMap.lineMap A B (min (a m) (b m))) = _
        rw [min_eq_left h.le, ← hav m]; exact ho1
      · show (D.tile (ee m).1).localAngle (AffineMap.lineMap A B (max (a m) (b m))) = _
        rw [max_eq_right h.le, ← hbv m]; exact ho2
    · obtain ⟨o, ho1, ho2⟩ := exists_OE_rev model _ (hcong (ee m).1) α hirr hA0 hA1 hA2 (ee m).2
      refine ⟨o, ?_, ?_⟩
      · show (D.tile (ee m).1).localAngle (AffineMap.lineMap A B (min (a m) (b m))) = _
        rw [min_eq_right h.le, ← hbv m]; exact ho1
      · show (D.tile (ee m).1).localAngle (AffineMap.lineMap A B (max (a m) (b m))) = _
        rw [max_eq_left h.le, ← hav m]; exact ho2
  choose oe hoe1 hoe2 using hoe
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
  -- the chain
  obtain ⟨i0, hi0⟩ := IntervalChain.first_starts_at_zero hCover (by norm_num)
  obtain ⟨r0, hr0⟩ := chain_exists hCover i0
  have claim : ∀ (r : List (Fin n)) (m : Fin n), Chain lo hi m r →
      ∃ L : List (LegStep N), RealLeg D α (ee m).1 (oe m) L ∧ (L = [] → r = []) ∧ ∃ z : Fin n,
        hi z = 1 ∧ lastTile (ee m).1 L = (ee z).1 ∧
        (legEdges (oe m) L).getLast (List.cons_ne_nil _ _) = oe z := by
    intro r
    induction r with
    | nil =>
      intro m hm
      exact ⟨[], trivial, fun _ => rfl, m, hm, rfl, rfl⟩
    | cons m' r ih =>
      intro m hm
      obtain ⟨hmm', hrest⟩ := hm
      obtain ⟨L', hL', -, z, hz1, hz2, hz3⟩ := ih m' hrest
      obtain ⟨hfr, hnv, hne⟩ := hjunc m m' hmm'
      refine ⟨⟨AffineMap.lineMap A B (hi m), (ee m').1, oe m'⟩ :: L', ?_,
        fun h => absurd h (List.cons_ne_nil _ _), z, hz1, ?_, ?_⟩
      · refine ⟨hfr, hnv, hne, hoe2 m, ?_, hL'⟩
        show (D.tile (ee m').1).localAngle (AffineMap.lineMap A B (hi m)) = angVal α (oe m').l
        rw [hmm']; exact hoe1 m'
      · exact hz2
      · rw [getLast_legEdges_cons]; exact hz3
  obtain ⟨L, hL, hLr, z, hz1, hz2, hz3⟩ := claim r0 i0 hr0
  refine ⟨(ee i0).1, oe i0, L, hL, ?_, ?_, ?_⟩
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

/-! ### 6. Corner arithmetic -/

theorem cnt_eq (α : ℝ) (hirr : Irrational (α / Real.pi)) (X Y Z : ℕ) (m n : ℤ)
    (h : (X : ℝ) * α + Y * (Real.pi - 3 * α) + Z * (2 * α) = (m : ℝ) * α + (n : ℝ) * Real.pi) :
    (X : ℤ) - 3 * Y + 2 * Z = m ∧ (Y : ℤ) = n := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have key : (((X : ℤ) - 3 * Y + 2 * Z - m : ℤ) : ℝ) * α = (((n : ℤ) - Y : ℤ) : ℝ) * Real.pi := by
    push_cast; linarith
  by_cases hk : ((X : ℤ) - 3 * Y + 2 * Z - m : ℤ) = 0
  · have h2 : (((n : ℤ) - Y : ℤ) : ℝ) * Real.pi = 0 := by rw [← key, hk]; simp
    have h3 : (((n : ℤ) - Y : ℤ) : ℝ) = 0 := by
      rcases mul_eq_zero.mp h2 with h | h
      · exact h
      · exact absurd h hpi
    have h4 : ((n : ℤ) - Y) = 0 := by exact_mod_cast h3
    omega
  · exfalso
    apply hirr
    refine ⟨(((n : ℤ) - Y : ℤ) : ℚ) / ((X : ℤ) - 3 * Y + 2 * Z - m : ℤ), ?_⟩
    have hk' : (((X : ℤ) - 3 * Y + 2 * Z - m : ℤ) : ℝ) ≠ 0 := by exact_mod_cast hk
    push_cast
    rw [div_eq_div_iff (by exact_mod_cast hk') hpi]
    push_cast at key
    linarith

theorem sum_of_values (α : ℝ) {ι : Type*} (S : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ S, f i = 0 ∨ ∃ a : Ang, f i = angVal α a) :
    ∃ X Y Z : ℕ, ∑ i ∈ S, f i = (X : ℝ) * α + Y * (Real.pi - 3 * α) + Z * (2 * α) := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨0, 0, 0, by simp⟩
  | insert x S hx ih =>
    obtain ⟨X, Y, Z, h⟩ := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    rw [Finset.sum_insert hx, h]
    rcases hf x (Finset.mem_insert_self _ _) with h0 | ⟨a, ha⟩
    · exact ⟨X, Y, Z, by rw [h0]; ring⟩
    · cases a
      · exact ⟨X + 1, Y, Z, by rw [ha]; simp only [angVal]; push_cast; ring⟩
      · exact ⟨X, Y + 1, Z, by rw [ha]; simp only [angVal]; push_cast; ring⟩
      · exact ⟨X, Y, Z + 1, by rw [ha]; simp only [angVal]; push_cast; ring⟩

/-- At a target vertex whose corner angle is `c < π`, a tile with positive local angle `angVal a`
leaves a nonnegative integer combination of `α, β, γ` for the others. -/
theorem corner_total {N : ℕ} (D : Dissection N) (model : Tri)
    (hcong : ∀ i, model.Congruent (D.tile i)) (α : ℝ)
    (hA0 : cornerAngle (model.pts 1) (model.pts 0) (model.pts 2) = α)
    (hA1 : cornerAngle (model.pts 2) (model.pts 1) (model.pts 0) = Real.pi - 3 * α)
    (hA2 : cornerAngle (model.pts 0) (model.pts 2) (model.pts 1) = 2 * α)
    (k : Fin 3) (c : ℝ)
    (hc : cornerAngle (D.target.pts (k + 1)) (D.target.pts k) (D.target.pts (k + 2)) = c)
    (hcpi : c < Real.pi) (t0 : Fin N) (a : Ang)
    (h : (D.tile t0).localAngle (D.target.pts k) = angVal α a) :
    ∃ X Y Z : ℕ, angVal α a + ((X : ℝ) * α + Y * (Real.pi - 3 * α) + Z * (2 * α)) = c := by
  classical
  let CD : CongruentDissection N := ⟨D, model, fun i => (hcong i).symm⟩
  have hmem : ∀ i, (D.tile i).localAngle (D.target.pts k) ∈
      ({α, Real.pi - 3 * α, 2 * α, Real.pi, 0} : Finset ℝ) :=
    fun i => Erdos634.Geometry.Dissection.congruentDissection_localAngle_mem CD α (Real.pi - 3 * α) (2 * α) hA0 hA1 hA2 k i
  have hsum : ∑ i, (D.tile i).localAngle (D.target.pts k) = c := by
    rw [Erdos634.VertexFigureReal.corner_angle_sum D k, hc]
  have hle : ∀ i, (D.tile i).localAngle (D.target.pts k) ≤ c := by
    intro i
    rw [← hsum]
    exact Finset.single_le_sum (f := fun i => (D.tile i).localAngle (D.target.pts k))
      (fun j _ => (D.tile j).localAngle_nonneg _) (Finset.mem_univ i)
  have hform : ∀ i ∈ Finset.univ.erase t0, (D.tile i).localAngle (D.target.pts k) = 0 ∨
      ∃ a : Ang, (D.tile i).localAngle (D.target.pts k) = angVal α a := by
    intro i _
    have hm := hmem i
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with h1 | h1 | h1 | h1 | h1
    · exact Or.inr ⟨.al, h1⟩
    · exact Or.inr ⟨.be, h1⟩
    · exact Or.inr ⟨.ga, h1⟩
    · have := hle i; rw [h1] at this; linarith
    · exact Or.inl h1
  obtain ⟨X, Y, Z, hXYZ⟩ := sum_of_values α (Finset.univ.erase t0)
    (fun i => (D.tile i).localAngle (D.target.pts k)) hform
  refine ⟨X, Y, Z, ?_⟩
  rw [← hXYZ, ← h, ← hsum]
  exact Finset.add_sum_erase _ (fun i => (D.tile i).localAngle (D.target.pts k)) (Finset.mem_univ t0)

/-- **First angle.**  If the target corner at the start of the side is `α`, the first tile's left angle
is `α`. -/
theorem corner_first {N : ℕ} (D : Dissection N) (model : Tri)
    (hcong : ∀ i, model.Congruent (D.tile i)) (α : ℝ) (hirr : Irrational (α / Real.pi))
    (hA0 : cornerAngle (model.pts 1) (model.pts 0) (model.pts 2) = α)
    (hA1 : cornerAngle (model.pts 2) (model.pts 1) (model.pts 0) = Real.pi - 3 * α)
    (hA2 : cornerAngle (model.pts 0) (model.pts 2) (model.pts 1) = 2 * α)
    (hα : 0 < α) (h3α : 3 * α < Real.pi) (k : Fin 3)
    (hc : cornerAngle (D.target.pts (k + 1)) (D.target.pts k) (D.target.pts (k + 2)) = α)
    (t0 : Fin N) (a : Ang) (h : (D.tile t0).localAngle (D.target.pts k) = angVal α a) :
    a = Ang.al := by
  obtain ⟨X, Y, Z, hs⟩ := corner_total D model hcong α hA0 hA1 hA2 k α hc (by linarith) t0 a h
  cases a
  · rfl
  · exfalso
    have := cnt_eq α hirr X (Y + 1) Z 1 0 (by simp only [angVal] at hs; push_cast; linarith)
    omega
  · exfalso
    have := cnt_eq α hirr X Y (Z + 1) 1 0 (by simp only [angVal] at hs; push_cast; linarith)
    omega

/-- **Last angle.**  If the target corner at the end of the side is `α`, `π − 3α` or `π − 2α`, the last
tile's right angle is `α` or `β`. -/
theorem corner_last {N : ℕ} (D : Dissection N) (model : Tri)
    (hcong : ∀ i, model.Congruent (D.tile i)) (α : ℝ) (hirr : Irrational (α / Real.pi))
    (hA0 : cornerAngle (model.pts 1) (model.pts 0) (model.pts 2) = α)
    (hA1 : cornerAngle (model.pts 2) (model.pts 1) (model.pts 0) = Real.pi - 3 * α)
    (hA2 : cornerAngle (model.pts 0) (model.pts 2) (model.pts 1) = 2 * α)
    (hα : 0 < α) (h3α : 3 * α < Real.pi) (k : Fin 3) (c : ℝ)
    (hc : cornerAngle (D.target.pts (k + 1)) (D.target.pts k) (D.target.pts (k + 2)) = c)
    (hcc : c = α ∨ c = Real.pi - 3 * α ∨ c = Real.pi - 2 * α)
    (t0 : Fin N) (a : Ang) (h : (D.tile t0).localAngle (D.target.pts k) = angVal α a) :
    a = Ang.al ∨ a = Ang.be := by
  have hcpi : c < Real.pi := by rcases hcc with h | h | h <;> rw [h] <;> linarith
  obtain ⟨X, Y, Z, hs⟩ := corner_total D model hcong α hA0 hA1 hA2 k c hc hcpi t0 a h
  cases a
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exfalso
    simp only [angVal] at hs
    rcases hcc with h1 | h1 | h1
    · have := cnt_eq α hirr X Y (Z + 1) 1 0 (by rw [h1] at hs; push_cast; linarith)
      omega
    · have := cnt_eq α hirr X Y (Z + 1) (-3) 1 (by rw [h1] at hs; push_cast; linarith)
      omega
    · have := cnt_eq α hirr X Y (Z + 1) (-2) 1 (by rw [h1] at hs; push_cast; linarith)
      omega

/-! ### 7. The assembled statement -/

/-- **A real leg along a side, with its counting identity.**  For a dissection into tiles congruent to
the `γ = 2α` model, a side of the target whose start corner is `α` and whose end corner is `α`, `π − 3α`
or `π − 2α`: there is a `RealLeg` along the side, and its middle multiplicities satisfy
`μ_β + 1 = q + ε`, `μ_α + 2μ_γ + 1 + ε = p + 2r` (`APrimeSeat1.counting_identity`). -/
theorem side_leg_counting {N : ℕ} (D : Dissection N) (model : Tri)
    (hcong : ∀ i, model.Congruent (D.tile i)) (α : ℝ) (hirr : Irrational (α / Real.pi))
    (hA0 : cornerAngle (model.pts 1) (model.pts 0) (model.pts 2) = α)
    (hA1 : cornerAngle (model.pts 2) (model.pts 1) (model.pts 0) = Real.pi - 3 * α)
    (hA2 : cornerAngle (model.pts 0) (model.pts 2) (model.pts 1) = 2 * α)
    (hα : 0 < α) (h3α : 3 * α < Real.pi) (i : Fin 3)
    (hcA : cornerAngle (D.target.pts (i + 1)) (D.target.pts i) (D.target.pts (i + 2)) = α)
    (c : ℝ)
    (hcB : cornerAngle (D.target.pts (i + 1 + 1)) (D.target.pts (i + 1)) (D.target.pts (i + 1 + 2)) = c)
    (hcc : c = α ∨ c = Real.pi - 3 * α ∨ c = Real.pi - 2 * α) :
    ∃ (t0 : Fin N) (e0 : OE) (r : List (LegStep N)), RealLeg D α t0 e0 r ∧
      ∃ steps : List (Cnt × OE), steps.map Prod.snd = r.map LegStep.e ∧ Valid e0 steps ∧
        muB steps + 1 = cntLetter isB (legEdges e0 r) +
          ((legEdges e0 r).getLast (List.cons_ne_nil _ _)).r.cnt.2.1 ∧
        muAG steps + 1 + ((legEdges e0 r).getLast (List.cons_ne_nil _ _)).r.cnt.2.1 =
          cntLetter isA (legEdges e0 r) + 2 * cntLetter isC (legEdges e0 r) ∧
      (r = [] → ∃ k : Fin 3, dist ((D.tile t0).pts k) ((D.tile t0).pts (k + 1)) =
        dist (D.target.pts i) (D.target.pts (i + 1))) := by
  obtain ⟨t0, e0, r, hleg, hfirst, hlast, hnil⟩ :=
    exists_chain_leg D model hcong α hirr hA0 hA1 hA2 i
  have h1 : e0.l = Ang.al :=
    corner_first D model hcong α hirr hA0 hA1 hA2 hα h3α i hcA t0 e0.l hfirst
  have h2 := corner_last D model hcong α hirr hA0 hA1 hA2 hα h3α (i + 1) c hcB hcc
    (lastTile t0 r) _ hlast
  obtain ⟨steps, hmap, hval, hid⟩ := RealLeg.counting_identity D model hcong α hirr hA0 hA1 hA2
    hα h3α r t0 e0 hleg h1 h2 _ rfl
  exact ⟨t0, e0, r, hleg, steps, hmap, hval, hid.1, hid.2, hnil⟩

end Erdos634.Draft.APrimeLegBuild

#print axioms Erdos634.Draft.APrimeLegBuild.exists_chain_leg
#print axioms Erdos634.Draft.APrimeLegBuild.side_leg_counting
