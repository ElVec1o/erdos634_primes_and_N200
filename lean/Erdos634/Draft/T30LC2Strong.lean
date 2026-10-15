import Mathlib.Tactic
import Erdos634.Draft.T30LPi3F6Corner

/-!
# Strengthened F6: third vertex identified, angles at both chord ends

`corner_chord_reflection_ex` and `aux_reflection_ex` are copies (same proofs) of `Pi3F6.corner_chord_reflection` / `aux_reflection`
(`T30LPi3F6`, `T30LPi3F6Corner`) whose conclusions additionally state: the third vertex of the corner tile is `X = pts (k₀+2)` (so the
far tile is `hull{P,Q,P+Q−O}` with `O` the corner), and the local angles at the chord ends: the corner tile `T` presents `(α,β)` or `(β,α)` at `(P,Q)` and
the far tile `T₂` the swapped pair (`T₂` presents at `P` what `T` presents at `Q`, and conversely).
-/

namespace Erdos634.Pi3F6

open Erdos634.Geometry Erdos634.Pi3Tile Erdos634.ChordFar Erdos634.Pi3Corner Erdos634.TPErdos

set_option maxHeartbeats 800000 in
open Erdos634.EdgeWordConversion in
/-- **F6: the far tile across the corner chord is the point reflection of the corner tile.** -/
theorem corner_chord_reflection_ex {N : ℕ} (D : CongruentDissection N) {α a b c : ℝ} (hirr : Irr α)
    (hS : D.model.SixtyData α a b c) (hac : a ≠ c) (hbc : b ≠ c)
    (hword : ∀ x y z : ℕ, (x : ℝ) * a + y * b + z * c = c → x + y + z = 1)
    (j0 : Fin N) (k0 : Fin 3) {P Q : Plane} (hP : (D.tile j0).pts k0 = P) (hQ : (D.tile j0).pts (k0 + 1) = Q)
    (hlen : dist P Q = c)
    (f : Plane →ₗ[ℝ] ℝ) (hf : f ≠ 0) (c0 : ℝ) (hfle : ∀ i, f ((D.tile j0).pts i) ≤ c0)
    (hfP : f P = c0) (hfQ : f Q = c0)
    (g : Plane →ₗ[ℝ] ℝ) (cg : ℝ) (hg : ∀ y ∈ D.target.carrier, g y ≤ cg)
    (hgP : g P = cg) (hgQ : g Q < cg)
    (h : Plane →ₗ[ℝ] ℝ) (ch : ℝ) (hh : ∀ y ∈ D.target.carrier, h y ≤ ch)
    (hhQ : h Q = ch) (hhP : h P < ch)
    (hint : openSegment ℝ P Q ⊆ interior D.target.carrier)
    (hPfr : P ∈ frontier D.target.carrier) (hPnv : P ∉ Set.range D.target.pts) :
    ∃ j : Fin N, j ≠ j0 ∧ ∃ X : Plane, X = (D.tile j0).pts (k0 + 2) ∧ f X < c0 ∧
      (D.tile j0).carrier = convexHull ℝ {P, Q, X} ∧
      (D.tile j).carrier = convexHull ℝ {P, Q, P + Q - X} ∧
      (∀ y ∈ (D.tile j).carrier, c0 ≤ f y) ∧
      (((D.tile j0).localAngle P = α ∧ (D.tile j0).localAngle Q = 2 * Real.pi / 3 - α) ∨
        ((D.tile j0).localAngle P = 2 * Real.pi / 3 - α ∧ (D.tile j0).localAngle Q = α)) ∧
      (D.tile j).localAngle P = (D.tile j0).localAngle Q ∧
      (D.tile j).localAngle Q = (D.tile j0).localAngle P := by
  have hPQ : P ≠ Q := by
    rw [← hP, ← hQ]
    intro hh'
    have := (D.tile j0).indep.injective hh'
    exact absurd this ((by decide : ∀ k : Fin 3, k ≠ k + 1) k0)
  have hwall : ∀ y ∈ openSegment ℝ P Q, ∀ i, y ∉ interior (D.tile i).carrier := by
    rw [← hP, ← hQ]; exact hwall_of_tile_edge D.toDissection j0 k0
  -- the far chain is a single `c`-edge
  obtain ⟨e2, he2, hch2, hlen2⟩ := far_chain_single_gen D (sideLen_mem D hS)
    hword f hf c0 hPQ hfP hfQ g cg hg hgP hgQ h ch hh hhQ hhP hint hwall hlen
  obtain ⟨j, k2⟩ := e2
  obtain ⟨hf2P, hf2Q, hle2⟩ := Dissection.mem_lineChain.mp he2
  have hsub := chain_edge_subset_chord D.toDissection (-f) (neg_ne_zero.mpr hf) (-c0) hPQ (by simp [hfP])
    (by simp [hfQ]) g cg hg hgP hgQ h ch hh hhQ hhP he2
  have hend := seg_endpoints hPQ (hsub (left_mem_segment ℝ _ _ : (D.tile j).pts k2 ∈ (D.tile j).edge k2))
    (hsub (right_mem_segment ℝ _ _ : (D.tile j).pts (k2 + 1) ∈ (D.tile j).edge k2))
    (by simpa [hlen] using hlen2)
  -- strictness and distinctness
  have hX : f ((D.tile j0).pts (k0 + 2)) < c0 :=
    third_strict (D.tile j0) f hf c0 hfle k0 (by rw [hP]; exact hfP) (by rw [hQ]; exact hfQ)
  have hX' : (-f) ((D.tile j).pts (k2 + 2)) < -c0 :=
    third_strict (D.tile j) (-f) (neg_ne_zero.mpr hf) (-c0) hle2 k2 hf2P hf2Q
  have hjne : j ≠ j0 := by
    rintro rfl
    have := hle2 (k0 + 2)
    simp only [LinearMap.neg_apply] at this
    linarith
  -- angles at `P`
  have hTc : dist ((D.tile j0).pts k0) ((D.tile j0).pts (k0 + 1)) = c := by rw [hP, hQ]; exact hlen
  have hTd := third_vertex (tile_sixty D hS j0) hac hbc k0 hTc
  have hT2c : dist ((D.tile j).pts k2) ((D.tile j).pts (k2 + 1)) = c := hlen2
  have hT2d := third_vertex (tile_sixty D hS j) hac hbc k2 hT2c
  have hlocT : (D.tile j0).localAngle P = (D.tile j0).angleAt k0 := by
    rw [← hP]; exact Tri.localAngle_vertex _ _
  have hαT : (D.tile j0).localAngle P = α ∨ (D.tile j0).localAngle P = 2 * Real.pi / 3 - α := by
    rw [hlocT]
    rcases hTd with ⟨-, h2, -, -⟩ | ⟨-, h2, -, -⟩
    · exact Or.inl h2
    · exact Or.inr h2
  have hdiff := angles_differ D hirr hS hPfr hPnv hjne.symm hαT
  -- legs swapped
  have hswap : dist P ((D.tile j).pts (k2 + 2)) = dist Q ((D.tile j0).pts (k0 + 2)) ∧
      dist Q ((D.tile j).pts (k2 + 2)) = dist P ((D.tile j0).pts (k0 + 2)) := by
    rw [hP, hQ] at hTd
    rcases hend with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · have hloc : (D.tile j).localAngle P = (D.tile j).angleAt k2 := by
        rw [← e1]; exact Tri.localAngle_vertex _ _
      rw [hlocT, hloc] at hdiff
      rw [e1, e2] at hT2d
      rcases hTd with ⟨t1, t2, t3, t4⟩ | ⟨t1, t2, t3, t4⟩ <;>
        rcases hT2d with ⟨u1, u2, u3, u4⟩ | ⟨u1, u2, u3, u4⟩ <;>
        first
        | exact absurd (t2.trans u2.symm) hdiff
        | exact ⟨by rw [← e1] at *; linarith, by linarith⟩
    · have hloc : (D.tile j).localAngle P = (D.tile j).angleAt (k2 + 1) := by
        rw [← e2]; exact Tri.localAngle_vertex _ _
      rw [hlocT, hloc] at hdiff
      rw [e1, e2] at hT2d
      rcases hTd with ⟨t1, t2, t3, t4⟩ | ⟨t1, t2, t3, t4⟩ <;>
        rcases hT2d with ⟨u1, u2, u3, u4⟩ | ⟨u1, u2, u3, u4⟩ <;>
        first
        | exact absurd (t2.trans u4.symm) hdiff
        | exact ⟨by linarith, by linarith⟩
  have hX'' : c0 < f ((D.tile j).pts (k2 + 2)) := by
    simp only [LinearMap.neg_apply] at hX'; linarith
  have hrefl := reflect_of_swapped f c0 hPQ hfP hfQ (by rw [← hP, ← hQ] at *; exact hX) hX'' hswap.1 hswap.2
  have hlocQ : (D.tile j0).localAngle Q = (D.tile j0).angleAt (k0 + 1) := by
    rw [← hQ]; exact Tri.localAngle_vertex _ _
  have hang : (((D.tile j0).localAngle P = α ∧ (D.tile j0).localAngle Q = 2 * Real.pi / 3 - α) ∨
        ((D.tile j0).localAngle P = 2 * Real.pi / 3 - α ∧ (D.tile j0).localAngle Q = α)) ∧
      (D.tile j).localAngle P = (D.tile j0).localAngle Q ∧
      (D.tile j).localAngle Q = (D.tile j0).localAngle P := by
    have hdiff' := hdiff
    rcases hend with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · have hl1 : (D.tile j).localAngle P = (D.tile j).angleAt k2 := by
        rw [← e1]; exact Tri.localAngle_vertex _ _
      have hl2 : (D.tile j).localAngle Q = (D.tile j).angleAt (k2 + 1) := by
        rw [← e2]; exact Tri.localAngle_vertex _ _
      rw [hlocT, hl1] at hdiff'
      rw [hlocT, hlocQ, hl1, hl2]
      rcases hTd with ⟨-, t2, -, t4⟩ | ⟨-, t2, -, t4⟩ <;> rcases hT2d with ⟨-, u2, -, u4⟩ | ⟨-, u2, -, u4⟩ <;>
        simp only [t2, t4, u2, u4, ne_eq, not_true_eq_false] at hdiff' ⊢ <;> try simp
    · have hl1 : (D.tile j).localAngle P = (D.tile j).angleAt (k2 + 1) := by
        rw [← e2]; exact Tri.localAngle_vertex _ _
      have hl2 : (D.tile j).localAngle Q = (D.tile j).angleAt k2 := by
        rw [← e1]; exact Tri.localAngle_vertex _ _
      rw [hlocT, hl1] at hdiff'
      rw [hlocT, hlocQ, hl1, hl2]
      rcases hTd with ⟨-, t2, -, t4⟩ | ⟨-, t2, -, t4⟩ <;> rcases hT2d with ⟨-, u2, -, u4⟩ | ⟨-, u2, -, u4⟩ <;>
        simp only [t2, t4, u2, u4, ne_eq, not_true_eq_false] at hdiff' ⊢ <;> try simp
  refine ⟨j, hjne, (D.tile j0).pts (k0 + 2), rfl, hX, ?_, ?_, ?_, hang.1, hang.2.1, hang.2.2⟩
  · unfold Tri.carrier; rw [range_pts_eq _ k0, hP, hQ]
  · unfold Tri.carrier; rw [range_pts_eq _ k2, hrefl]
    rcases hend with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · rw [e1, e2]
    · rw [e1, e2, Set.insert_comm]
  · intro y hy
    have := Tri.carrier_subset_halfplane (D.tile j) (-f) (-c0) hle2 y hy
    simp only [LinearMap.neg_apply] at this; linarith


set_option maxHeartbeats 800000 in
theorem aux_reflection_ex {N : ℕ} (D : CongruentDissection N) {α a b c : ℝ} (hirr : Irr α)
    (hS : D.model.SixtyData α a b c) (hac : a ≠ c) (hbc : b ≠ c)
    (hword : ∀ x y z : ℕ, (x : ℝ) * a + y * b + z * c = c → x + y + z = 1)
    (i : Fin N) (j : Fin 3) (v w z : Fin 3) (hvw : v ≠ w) (hvz : v ≠ z) (hwz : w ≠ z)
    (hjv : (D.tile i).pts j = D.target.pts v) (hang : (D.tile i).angleAt j = Real.pi / 3)
    {p r : ℝ} (hp0 : 0 < p) (hr0 : 0 < r)
    (hP : (D.tile i).pts (j + 1) - D.target.pts v = p • (D.target.pts w - D.target.pts v))
    (hQ : (D.tile i).pts (j + 2) - D.target.pts v = r • (D.target.pts z - D.target.pts v))
    (hPA : (D.tile i).pts (j + 1) ≠ D.target.pts w) (hQB : (D.tile i).pts (j + 2) ≠ D.target.pts z) :
    ∃ j' : Fin N, j' ≠ i ∧
      (D.tile j').carrier = convexHull ℝ {(D.tile i).pts (j + 1), (D.tile i).pts (j + 2),
        (D.tile i).pts (j + 1) + (D.tile i).pts (j + 2) - (D.tile i).pts j} ∧
      (((D.tile i).localAngle ((D.tile i).pts (j + 1)) = α ∧
          (D.tile i).localAngle ((D.tile i).pts (j + 2)) = 2 * Real.pi / 3 - α) ∨
        ((D.tile i).localAngle ((D.tile i).pts (j + 1)) = 2 * Real.pi / 3 - α ∧
          (D.tile i).localAngle ((D.tile i).pts (j + 2)) = α)) ∧
      (D.tile j').localAngle ((D.tile i).pts (j + 1)) = (D.tile i).localAngle ((D.tile i).pts (j + 2)) ∧
      (D.tile j').localAngle ((D.tile i).pts (j + 2)) = (D.tile i).localAngle ((D.tile i).pts (j + 1)) := by
  set T := D.target with hT
  set P := (D.tile i).pts (j + 1) with hPdef
  set Q := (D.tile i).pts (j + 2) with hQdef
  have hPform : P = (1 - p) • T.pts v + p • T.pts w := by
    have : P = T.pts v + p • (T.pts w - T.pts v) := by rw [← hP]; abel
    rw [this]; simp only [smul_sub, sub_smul, one_smul]; abel
  have hQform : Q = (1 - r) • T.pts v + r • T.pts z := by
    have : Q = T.pts v + r • (T.pts z - T.pts v) := by rw [← hQ]; abel
    rw [this]; simp only [smul_sub, sub_smul, one_smul]; abel
  have hcd : ∀ (m n : Fin 3), T.basis.coord m (T.pts n) = if m = n then 1 else 0 :=
    fun m n => AffineBasis.coord_apply T.basis m n
  have hPmem : P ∈ T.carrier := Erdos634.BaseSelection.tile_subset_target D.toDissection i
    (subset_convexHull ℝ _ ⟨j + 1, rfl⟩)
  have hQmem : Q ∈ T.carrier := Erdos634.BaseSelection.tile_subset_target D.toDissection i
    (subset_convexHull ℝ _ ⟨j + 2, rfl⟩)
  have hp1 : p < 1 := by
    have hmem' := hPmem
    rw [T.carrier_eq_nonneg_coord] at hmem'
    have hnn : 0 ≤ T.basis.coord v P := hmem' v
    rw [hPform, aff_comb _ _ _ _ _ (by ring), hcd, hcd] at hnn
    simp [hvw] at hnn
    rcases lt_or_eq_of_le (by linarith : p ≤ 1) with h | h
    · exact h
    · exfalso; apply hPA; rw [hPform, h]; simp
  have hr1 : r < 1 := by
    have hmem' := hQmem
    rw [T.carrier_eq_nonneg_coord] at hmem'
    have hnn : 0 ≤ T.basis.coord v Q := hmem' v
    rw [hQform, aff_comb _ _ _ _ _ (by ring), hcd, hcd] at hnn
    simp [hvz] at hnn
    rcases lt_or_eq_of_le (by linarith : r ≤ 1) with h | h
    · exact h
    · exfalso; apply hQB; rw [hQform, h]; simp
  obtain ⟨⟨g, cg, hg, hgP, hgQ, hg0⟩, ⟨h, ch, hh, hhQ, hhP, hh0⟩, hint, hfr, hnv, -, -⟩ :=
    clamps T v w z hvw hvz hwz hp0 hp1 hr0 hr1
  have hlen : dist P Q = c := by
    have := opp_c_of_pi3 hirr (tile_sixty D hS i) j hang
    unfold Tri.oppLen at this
    exact this
  obtain ⟨f, c0, hf, hfle, hf1, hf2, hf3⟩ := exists_supporting (D.tile i) (j + 1)
  have hfle' : ∀ m, f ((D.tile i).pts m) ≤ c0 := fun m => hfle _ (subset_convexHull ℝ _ ⟨m, rfl⟩)
  have e11 : j + 1 + 1 = j + 2 := (by decide : ∀ j : Fin 3, j + 1 + 1 = j + 2) j
  rw [e11] at hf2
  obtain ⟨j', hj', X, hXO, -, hcar1, hcar2, -, hang, hl1, hl2⟩ := corner_chord_reflection_ex D hirr hS hac hbc hword i (j + 1)
    (P := P) (Q := Q) rfl (by rw [e11]) hlen f hf c0 hfle' hf1 hf2 g cg hg (by rw [hPform]; exact hgP) (by rw [hQform]; exact hgQ)
    h ch hh (by rw [hQform]; exact hhQ) (by rw [hPform]; exact hhP)
    (by rw [hPform, hQform]; exact hint) (by rw [hPform]; exact hfr) (by rw [hPform]; exact hnv)
  have e12 : j + 1 + 2 = j := (by decide : ∀ j : Fin 3, j + 1 + 2 = j) j
  rw [e12] at hXO
  rw [hXO] at hcar2
  exact ⟨j', hj', hcar2, hang, hl1, hl2⟩

end Erdos634.Pi3F6

#print axioms Erdos634.Pi3F6.corner_chord_reflection_ex
#print axioms Erdos634.Pi3F6.aux_reflection_ex
