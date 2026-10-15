import Mathlib.Tactic
import Erdos634.Draft.GLICorner

/-!
# The apex: the two legs end with one `α` and one `β`

At the apex `r` (target angle `π − 2α`), the last tiles of the two leg chains have local angles in `{α, β}` (not `γ`), are DISTINCT tiles
(`apex_tiles_ne`: if one tile had edges on both legs at `r`, its angle at `r` would be the apex angle `π − 2α ∉ {α, β, γ}`),
and at most one tile presents `α` and at most one `β` at `r`; hence `apex_pair`: one leg ends with `α`, the other with `β`.
-/

namespace Erdos634.GLI

open Erdos634.Geometry Erdos634.Placement Erdos634.OrientBridge Erdos634.ChainInstance Erdos634.GLG
  Erdos634.BaseChain

variable {N : ℕ}

theorem seg_vec {a b x : Plane} (hx : x ∈ segment ℝ a b) (hxb : x ≠ b) :
    ∃ t : ℝ, 0 < t ∧ x - b = t • (a - b) := by
  obtain ⟨s, t', hs, ht, hst, rfl⟩ := hx
  have ht' : t' = 1 - s := by linarith
  subst ht'
  refine ⟨s, lt_of_le_of_ne hs ?_, by module⟩
  intro h0
  apply hxb; rw [← h0]; simp

theorem seg_inter (T : Tri) {p q r : Fin 3} (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) {y : Plane}
    (h1 : y ∈ segment ℝ (T.pts p) (T.pts r)) (h2 : y ∈ segment ℝ (T.pts q) (T.pts r)) :
    y = T.pts r := by
  have hq0 : T.basis.coord q y = 0 := by
    have hm : T.basis.coord q y ∈ segment ℝ (T.basis.coord q (T.pts p)) (T.basis.coord q (T.pts r)) := by
      rw [← image_segment ℝ (T.basis.coord q)]; exact Set.mem_image_of_mem _ h1
    rw [Erdos634.Draft.NearBaseVertex.coord_other T hpq.symm,
      Erdos634.Draft.NearBaseVertex.coord_other T hqr, segment_same] at hm
    exact hm
  have hp0 : T.basis.coord p y = 0 := by
    have hm : T.basis.coord p y ∈ segment ℝ (T.basis.coord p (T.pts q)) (T.basis.coord p (T.pts r)) := by
      rw [← image_segment ℝ (T.basis.coord p)]; exact Set.mem_image_of_mem _ h2
    rw [Erdos634.Draft.NearBaseVertex.coord_other T hpq,
      Erdos634.Draft.NearBaseVertex.coord_other T hpr, segment_same] at hm
    exact hm
  have hz : ∀ i : Fin 3, i ≠ r → T.basis.coord i y = 0 := by
    intro i hi
    have : i = p ∨ i = q :=
      (by decide : ∀ p q r i : Fin 3, p ≠ q → p ≠ r → q ≠ r → i ≠ r → i = p ∨ i = q) p q r i hpq hpr hqr hi
    rcases this with rfl | rfl
    · exact hp0
    · exact hq0
  have hsum := T.basis.sum_coord_apply_eq_one (k := ℝ) y
  have hr1 : T.basis.coord r y = 1 := by
    rw [Finset.sum_eq_single r (fun i _ hi => hz i hi) (by simp)] at hsum
    exact hsum
  apply T.basis.ext_elem
  intro i
  by_cases hi : i = r
  · subst hi; rw [hr1, Erdos634.Draft.NearBaseVertex.coord_self]
  · rw [hz i hi, Erdos634.Draft.NearBaseVertex.coord_other T hi]

theorem corner_scale (c x y x' y' : Plane) {s t : ℝ} (hs : 0 < s) (ht : 0 < t)
    (hx : x' - c = s • (x - c)) (hy : y' - c = t • (y - c)) :
    cornerAngle x' c y' = cornerAngle x c y := by
  unfold cornerAngle EuclideanGeometry.angle
  simp only [vsub_eq_sub]
  rw [hx, hy, InnerProductGeometry.angle_smul_left_of_pos _ _ hs,
    InnerProductGeometry.angle_smul_right_of_pos _ _ ht]

theorem cornerAngle_comm' (x c y : Plane) : cornerAngle x c y = cornerAngle y c x := by
  unfold cornerAngle; exact EuclideanGeometry.angle_comm _ _ _

theorem edgeWest_mem {D : Dissection N} (dir : Plane →ₗ[ℝ] ℝ) (e : Fin N × Fin 3) :
    edgeWest D dir e ∈ D.target.carrier :=
  tile_subset_target D e.1 (by
    unfold edgeWest; split_ifs <;> exact subset_convexHull ℝ _ (Set.mem_range_self _))

theorem apex_tiles_ne (D : CongruentDissection N) {α a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (h : D.model.TwoAlphaData α a b c)
    {p q r : Fin 3} (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (hr : D.target.angleAt r = Real.pi - 2 * α)
    {wA wB : Wall D.toDissection} {EA EB : ℕ → Fin N × Fin 3} {nA nB : ℕ}
    (CA : IsChain wA EA nA) (CB : IsChain wB EB nB)
    (hAa : wA.a = D.target.pts p) (hAb : wA.b = D.target.pts r)
    (hBa : wB.a = D.target.pts q) (hBb : wB.b = D.target.pts r) :
    (EA (nA - 1)).1 ≠ (EB (nB - 1)).1 := by
  intro hT
  obtain ⟨hα0, -, -⟩ := Row4.model_sides D h
  have hπ := Real.pi_pos
  have hnA : nA - 1 < nA := by have := CA.n_pos; omega
  have hnB : nB - 1 < nB := by have := CB.n_pos; omega
  set eA := EA (nA - 1) with heA
  set eB := EB (nB - 1) with heB
  have hEA : edgeEast D.toDissection wA.dir eA = D.target.pts r := by rw [heA, CA.east_last, hAb]
  have hEB : edgeEast D.toDissection wB.dir eB = D.target.pts r := by rw [heB, CB.east_last, hBb]
  have hltA : wA.dir (edgeWest D.toDissection wA.dir eA) < wA.dir (D.target.pts r) := by
    have := CA.nondeg (nA - 1) hnA
    rw [← dir_edgeWest, ← dir_edgeEast, ← heA, hEA] at this; exact this
  have hltB : wB.dir (edgeWest D.toDissection wB.dir eB) < wB.dir (D.target.pts r) := by
    have := CB.nondeg (nB - 1) hnB
    rw [← dir_edgeWest, ← dir_edgeEast, ← heB, hEB] at this; exact this
  set WA := edgeWest D.toDissection wA.dir eA with hWA
  set WB := edgeWest D.toDissection wB.dir eB with hWB
  have hWAr : WA ≠ D.target.pts r := fun e => by rw [e] at hltA; exact lt_irrefl _ hltA
  have hWBr : WB ≠ D.target.pts r := fun e => by rw [e] at hltB; exact lt_irrefl _ hltB
  have hsegA : WA ∈ segment ℝ (D.target.pts p) (D.target.pts r) := by
    have := wA.hface WA (edgeWest_mem _ _) (CA.edgeWest_on_wall hnA)
    rwa [hAa, hAb] at this
  have hsegB : WB ∈ segment ℝ (D.target.pts q) (D.target.pts r) := by
    have := wB.hface WB (edgeWest_mem _ _) (CB.edgeWest_on_wall hnB)
    rwa [hBa, hBb] at this
  have hWAB : WA ≠ WB := fun e => hWAr (seg_inter D.target hpq hpr hqr hsegA (e ▸ hsegB))
  -- vertices of the common tile
  obtain ⟨iA, hiA⟩ : ∃ i : Fin 3, (D.tile eA.1).pts i = WA := ⟨_, pts_west D.toDissection wA.dir eA⟩
  obtain ⟨v, hv⟩ : ∃ i : Fin 3, (D.tile eA.1).pts i = D.target.pts r :=
    ⟨_, (pts_east D.toDissection wA.dir eA).trans hEA⟩
  obtain ⟨iB, hiB⟩ : ∃ i : Fin 3, (D.tile eA.1).pts i = WB := by
    refine ⟨westIdx wB.dir (D.tile eA.1) eB.2, ?_⟩
    have := pts_west D.toDissection wB.dir eB
    rw [← hT] at this; exact this
  have hinj := (D.tile eA.1).indep.injective
  have hAv : iA ≠ v := fun e => hWAr (by rw [← hiA, e, hv])
  have hBv : iB ≠ v := fun e => hWBr (by rw [← hiB, e, hv])
  have hAB : iA ≠ iB := fun e => hWAB (by rw [← hiA, ← hiB, e])
  have hcase : (iA = v + 1 ∧ iB = v + 2) ∨ (iA = v + 2 ∧ iB = v + 1) :=
    (by decide : ∀ v vA vB : Fin 3, vA ≠ v → vB ≠ v → vA ≠ vB →
      (vA = v + 1 ∧ vB = v + 2) ∨ (vA = v + 2 ∧ vB = v + 1)) v iA iB hAv hBv hAB
  obtain ⟨tA, htA, hvA⟩ := seg_vec hsegA hWAr
  obtain ⟨tB, htB, hvB⟩ := seg_vec hsegB hWBr
  have hang : (D.tile eA.1).angleAt v = cornerAngle (D.target.pts p) (D.target.pts r) (D.target.pts q) := by
    have hs := corner_scale (D.target.pts r) (D.target.pts p) (D.target.pts q) WA WB htA htB hvA hvB
    unfold Tri.angleAt
    rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [← h1, ← h2, hiA, hiB, hv]; exact hs
    · rw [← h1, ← h2, hiA, hiB, hv]; rw [cornerAngle_comm']; exact hs
  have htar : D.target.angleAt r = cornerAngle (D.target.pts p) (D.target.pts r) (D.target.pts q) := by
    have hc : (p = r + 1 ∧ q = r + 2) ∨ (p = r + 2 ∧ q = r + 1) :=
      (by decide : ∀ p q r : Fin 3, p ≠ q → p ≠ r → q ≠ r → (p = r + 1 ∧ q = r + 2) ∨ (p = r + 2 ∧ q = r + 1))
        p q r hpq hpr hqr
    unfold Tri.angleAt
    rcases hc with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [← h1, ← h2]
    · rw [← h1, ← h2]; exact cornerAngle_comm' _ _ _
  have hfin : (D.tile eA.1).angleAt v = Real.pi - 2 * α := by rw [hang, ← htar, hr]
  have d1 : α ≠ Real.pi - 3 * α := fun e => hα ⟨1 / 4, by push_cast; linarith⟩
  rcases Row4.tile_angle_mem D h eA.1 v with e | e | e
  · rw [e] at hfin; exact hα ⟨1 / 3, by push_cast; linarith⟩
  · rw [e] at hfin; linarith
  · rw [e] at hfin; exact hα ⟨1 / 4, by push_cast; linarith⟩

theorem apex_alpha_unique (D : CongruentDissection N) {α a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (h : D.model.TwoAlphaData α a b c) {r : Fin 3}
    (hr : D.target.angleAt r = Real.pi - 2 * α) (i j : Fin N)
    (hi : (D.tile i).localAngle (D.target.pts r) = α) (hj : (D.tile j).localAngle (D.target.pts r) = α) :
    i = j := by
  obtain ⟨hα0, hα3, -⟩ := Row4.model_sides D h
  have hc := Row4.count_eq D hα h hα0 hα3 (D.target.pts r)
  rw [D.target.localAngle_vertex r] at hc
  change D.target.angleAt r = _ at hc
  rw [hr] at hc
  set P := ({i | (D.tile i).localAngle (D.target.pts r) = α} : Finset (Fin N)).card
  set Q := ({i | (D.tile i).localAngle (D.target.pts r) = Real.pi - 3 * α} : Finset (Fin N)).card
  set R := ({i | (D.tile i).localAngle (D.target.pts r) = 2 * α} : Finset (Fin N)).card
  set S := ({i | (D.tile i).localAngle (D.target.pts r) = Real.pi} : Finset (Fin N)).card
  set T := ({i | (D.tile i).localAngle (D.target.pts r) = 2 * Real.pi} : Finset (Fin N)).card
  obtain ⟨h1, h2⟩ := Row4.fig_arith hα (P := P) (Q := Q) (R := R) (S := S) (T := T) (j := 1)
    (k := -2) (by push_cast; linear_combination -hc)
  have hP : P ≤ 1 := by omega
  have hi' : i ∈ ({i | (D.tile i).localAngle (D.target.pts r) = α} : Finset (Fin N)) := by simp [hi]
  have hj' : j ∈ ({i | (D.tile i).localAngle (D.target.pts r) = α} : Finset (Fin N)) := by simp [hj]
  exact Finset.card_le_one.mp hP i hi' j hj'

theorem apex_pair (D : CongruentDissection N) {α a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (h : D.model.TwoAlphaData α a b c)
    {p q r : Fin 3} (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (hr : D.target.angleAt r = Real.pi - 2 * α)
    {wA wB : Wall D.toDissection} {EA EB : ℕ → Fin N × Fin 3} {nA nB : ℕ}
    (CA : IsChain wA EA nA) (CB : IsChain wB EB nB)
    (hAa : wA.a = D.target.pts p) (hAb : wA.b = D.target.pts r)
    (hBa : wB.a = D.target.pts q) (hBb : wB.b = D.target.pts r) :
    (eAng D.toDissection wA.dir (EA (nA - 1)) = α ∧
        eAng D.toDissection wB.dir (EB (nB - 1)) = Real.pi - 3 * α) ∨
    (eAng D.toDissection wA.dir (EA (nA - 1)) = Real.pi - 3 * α ∧
        eAng D.toDissection wB.dir (EB (nB - 1)) = α) := by
  obtain ⟨hα0, hα3, -⟩ := Row4.model_sides D h
  obtain ⟨hBγ, hBβ⟩ := Row4.corner_B D hα h hα0 hα3 hr
  have hne := apex_tiles_ne D hα h hpq hpr hqr hr CA CB hAa hAb hBa hBb
  have hnA : nA - 1 < nA := by have := CA.n_pos; omega
  have hnB : nB - 1 < nB := by have := CB.n_pos; omega
  have hlocA : (D.tile (EA (nA - 1)).1).localAngle (D.target.pts r) =
      eAng D.toDissection wA.dir (EA (nA - 1)) := by
    rw [← hAb, ← CA.east_last, ← pts_east, Tri.localAngle_vertex]; rfl
  have hlocB : (D.tile (EB (nB - 1)).1).localAngle (D.target.pts r) =
      eAng D.toDissection wB.dir (EB (nB - 1)) := by
    rw [← hBb, ← CB.east_last, ← pts_east, Tri.localAngle_vertex]; rfl
  have mA : eAng D.toDissection wA.dir (EA (nA - 1)) = α ∨
      eAng D.toDissection wA.dir (EA (nA - 1)) = Real.pi - 3 * α ∨
      eAng D.toDissection wA.dir (EA (nA - 1)) = 2 * α := Row4.tile_angle_mem D h _ _
  have mB : eAng D.toDissection wB.dir (EB (nB - 1)) = α ∨
      eAng D.toDissection wB.dir (EB (nB - 1)) = Real.pi - 3 * α ∨
      eAng D.toDissection wB.dir (EB (nB - 1)) = 2 * α := Row4.tile_angle_mem D h _ _
  have gA := hBγ (EA (nA - 1)).1
  have gB := hBγ (EB (nB - 1)).1
  rw [hlocA] at gA
  rw [hlocB] at gB
  rcases mA with eA | eA | eA <;> rcases mB with eB | eB | eB
  · exact absurd (apex_alpha_unique D hα h hr _ _ (hlocA.trans eA) (hlocB.trans eB)) hne
  · exact Or.inl ⟨eA, eB⟩
  · exact absurd eB gB
  · exact Or.inr ⟨eA, eB⟩
  · exact absurd (hBβ _ _ (hlocA.trans eA) (hlocB.trans eB)) hne
  · exact absurd eB gB
  · exact absurd eA gA
  · exact absurd eA gA
  · exact absurd eA gA

end Erdos634.GLI

#print axioms Erdos634.GLI.apex_pair
#print axioms Erdos634.GLI.seg_inter
