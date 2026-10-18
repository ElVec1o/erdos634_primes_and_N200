import Mathlib.Tactic
import Erdos634.Draft.ThmDLegBig

/-!
Credit: the method (rigidity window, Lemmas 30-34, row induction, Theorem 37) is adapted from M. Beeson and G. Rosu, 'Tiling a triangle into a prime number of congruent triangles' (preprint, 16 Oct 2026); the transfer to the tile with gamma = 2 alpha (fan lemma at straight points, windows u and v, Lemma K) is ours.

# Theorem D' (ThmDGeo, item (3)): the apex ends of the base leg  

`apex_start` : the base corner `Q` of the frame is the APEX of the target (corner angle `π - 2α`).  A `c>` block of `n < u` edges at the first edge,
stopped at its far end, is impossible: the tile `T₀` across the `b`-ray of the first tile is `apex_ray_tile` (the α-tile and the β-tile of the apex),
then `lemma33_interior` (window `u`).  `apex_end` is the mirror at `B` (`ε = -1`).  Hypotheses (the frame arithmetic of the apex): the ray
`lp 0 1` lies strictly inside the wedge: `hwedge`.
-/

namespace Erdos634.Draft.ThmDRun

open Erdos634.Geometry Erdos634.CertCoord Erdos634.Draft.SideRun Erdos634.Draft.APrimeLegBuild
  Erdos634.Draft.APrimeSeat1 Erdos634.Draft.APrimeLeg Erdos634.MarchSlots Set

variable {N : ℕ} {D : CongruentDissection N} {u v : ℕ} {α β γ L ax ay : ℝ}

theorem apex_start (S : SetupT D u v α β γ L ax ay) {W : List OE} {f : ℕ → ℝ} (hB : Brk S W f)
    (hnoγ : ∀ (t : Fin N) (k : Fin 3), (D.tile t).pts k ∈ Set.range D.target.pts →
      (D.tile t).localAngle ((D.tile t).pts k) ≠ γ)
    (hapex : cornerAngle (D.target.pts (0 + 1)) (D.target.pts 0) (D.target.pts (0 + 2)) = Real.pi - 2 * α)
    (hwedge : 0 < ay * ((u : ℝ) * v - uuT (u : ℝ) (v : ℝ)) - ax * hhT (u : ℝ) (v : ℝ))
    {n : ℕ} (hn1 : 1 ≤ n) (hnu : n < u) (hnW : n ≤ W.length)
    (hcp : ∀ j < n, W[j]? = some OE.cp)
    (hstop : n = W.length ∨ ∃ o, W[n]? = some o ∧ o.l = Ang.ga) : False := by
  have hL := S.hL
  have hu := S.u0
  have huv := S.uv'
  have hv2 := S.v2
  have hε : (1 : ℝ) ^ 2 = 1 := by norm_num
  have C : CtxBaseT D u v α β γ L ax ay 1 (f 0 * L) := ⟨S, Or.inl rfl⟩
  have hcp' : ∀ j < n, W[0 + j]? = some OE.cp := by intro j hj; simpa using hcp j hj
  obtain ⟨hpos, hrun⟩ := blk_cp S hB (a := 0) (n := n) (by omega) hcp'
  obtain ⟨hVnv, hst⟩ := cp_stop S hB hn1 (a := 0) (by omega) hcp' hnoγ (by simpa using hstop)
  have hx : f 0 * L = 0 := by rw [hB.f0]; ring
  have hX0 : lpT (u : ℝ) (v : ℝ) 1 (f 0 * L) 0 0 = mkPt 0 0 := by
    rw [lpT_base, hx]; exact mkPt_congr (by ring) rfl
  obtain ⟨t1, k, m, j, hkm, hkj, hmj, hk, hm, hj⟩ := hrun 0 (by omega)
  simp only [Nat.cast_zero, zero_add] at hk hm hj
  have hQm : mkPt 0 0 ∈ D.target.carrier := by
    rw [← hX0, ← hk]; exact Erdos634.MarchInduction.pts_mem_target D.toDissection t1 k
  have hYm : lpT (u : ℝ) (v : ℝ) 1 (f 0 * L) 0 1 ∈ D.target.carrier := by
    rw [← hj]; exact Erdos634.MarchInduction.pts_mem_target D.toDissection t1 j
  have hYpt : lpT (u : ℝ) (v : ℝ) 1 (f 0 * L) 0 1 =
      mkPt ((u : ℝ) * v - uuT (u : ℝ) (v : ℝ)) (hhT (u : ℝ) (v : ℝ)) := by
    rw [hx]; unfold lpT; exact mkPt_congr (by ring) (by ring)
  have hY1 : 0 < (lpT (u : ℝ) (v : ℝ) 1 (f 0 * L) 0 1) 1 := by
    rw [lpT_snd]; have := hhT_pos hu huv hv2; linarith
  have hint1 : openSegment ℝ (mkPt 0 0) (lpT (u : ℝ) (v : ℝ) 1 (f 0 * L) 0 1) ⊆ interior D.target.carrier := by
    refine S.interior_seg hQm hYm (Or.inr hY1) (Or.inr ?_) (Or.inl ?_)
    · rw [hYpt, gA_mk]; exact hwedge.trans_le (le_of_eq (by ring))
    · rw [gB_mk]; nlinarith [S.hay]
  have htot : ∑ i, (D.tile i).localAngle (lpT (u : ℝ) (v : ℝ) 1 (f 0 * L) 0 0) = Real.pi - 2 * α := by
    rw [hX0]
    have h0 : (mkPt 0 0 : Plane) = D.toDissection.target.pts 0 := ((target_pts01 S).1).symm
    rw [h0, vertex_total D.toDissection 0]
    exact hapex
  have hα1 : (D.tile t1).localAngle (lpT (u : ℝ) (v : ℝ) 1 (f 0 * L) 0 0) = α := by
    have hU : HasV D t1 (lpT (u : ℝ) (v : ℝ) 1 (f 0 * L) 0 0) (lpT (u : ℝ) (v : ℝ) 1 (f 0 * L) 1 0)
        (lpT (u : ℝ) (v : ℝ) 1 (f 0 * L) 0 1) := ⟨k, m, j, hkm, hkj, hmj, hk, hm, hj⟩
    exact (U_anglesT hu huv hv2 hε S.tile.hab S.tile.ac S.tile.bc S.hM (by simpa using hU)).1
  have hint : openSegment ℝ (lpT (u : ℝ) (v : ℝ) 1 (f 0 * L) 0 0) (lpT (u : ℝ) (v : ℝ) 1 (f 0 * L) 0 1) ⊆
      interior D.target.carrier := by
    rw [hX0]; exact hint1
  obtain ⟨hRay, -⟩ := apex_ray_tile S (X0 := lpT (u : ℝ) (v : ℝ) 1 (f 0 * L) 0 0) (fun p : Plane => p 1)
    phi_y_lineMap (fun q hq => (S.mem hq).1) (by rw [hX0]; rfl) hY1 hint htot (t1 := t1) (k := k) (m := j) (j := m)
    hkj hkm (Ne.symm hmj) hk hj hα1
  have hch : ∀ j : ℕ, 1 ≤ j → lpT (u : ℝ) (v : ℝ) 1 (f 0 * L) 0 (j : ℝ) ∈ D.target.carrier →
      openSegment ℝ (lpT (u : ℝ) (v : ℝ) 1 (f 0 * L) 0 0) (lpT (u : ℝ) (v : ℝ) 1 (f 0 * L) 0 (j : ℝ)) ⊆
        interior D.target.carrier := by
    intro j hj hjm
    rw [hX0]
    have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
    refine S.interior_seg hQm hjm (Or.inr ?_) (Or.inr ?_) (Or.inl ?_)
    · rw [lpT_snd]; have := hhT_pos hu huv hv2; nlinarith
    · have : lpT (u : ℝ) (v : ℝ) 1 (f 0 * L) 0 (j : ℝ) =
          mkPt ((j : ℝ) * ((u : ℝ) * v - uuT (u : ℝ) (v : ℝ))) ((j : ℝ) * hhT (u : ℝ) (v : ℝ)) := by
        rw [hx]; unfold lpT; exact mkPt_congr (by ring) rfl
      rw [this, gA_mk]
      nlinarith
    · rw [gB_mk]; nlinarith [S.hay]
  rw [hm] at hRay
  exact lemma33_interior C hn1 hnu hrun hch (hT0_of_ray C hRay) hVnv hnoγ hst

#print axioms apex_start
theorem apex_end (S : SetupT D u v α β γ L ax ay) {W : List OE} {f : ℕ → ℝ} (hB : Brk S W f)
    (hnoγ : ∀ (t : Fin N) (k : Fin 3), (D.tile t).pts k ∈ Set.range D.target.pts →
      (D.tile t).localAngle ((D.tile t).pts k) ≠ γ)
    (hapex : cornerAngle (D.target.pts (1 + 1)) (D.target.pts 1) (D.target.pts (1 + 2)) = Real.pi - 2 * α)
    (hwedge : 0 < ay * ((u : ℝ) * v - uuT (u : ℝ) (v : ℝ)) - (L - ax) * hhT (u : ℝ) (v : ℝ))
    {n : ℕ} (hn1 : 1 ≤ n) (hnu : n < u) (hn : n ≤ W.length)
    (hcm : ∀ j < n, W[W.length - 1 - j]? = some OE.cm)
    (hstop : n < W.length → ∃ o, W[W.length - 1 - n]? = some o ∧ o.r = Ang.ga) : False := by
  have hL := S.hL
  have hu := S.u0
  have huv := S.uv'
  have hv2 := S.v2
  have hε : (-1 : ℝ) ^ 2 = 1 := by norm_num
  have C : CtxBaseT D u v α β γ L ax ay (-1) (f W.length * L) := ⟨S, Or.inr rfl⟩
  obtain ⟨hpos, hrun⟩ := blk_cm S hB (b := W.length) (n := n) le_rfl hn hcm
  obtain ⟨hVnv, hst⟩ := cm_stop S hB hn1 (b := W.length) le_rfl hn hcm hnoγ (by
    rcases eq_or_lt_of_le hn with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h, hstop h⟩)
  have hx : f W.length * L = L := by rw [hB.fl]; ring
  have hX0 : lpT (u : ℝ) (v : ℝ) (-1) (f W.length * L) 0 0 = mkPt L 0 := by
    rw [lpT_base, hx]; exact mkPt_congr (by ring) rfl
  obtain ⟨t1, k, m, j, hkm, hkj, hmj, hk, hm, hj⟩ := hrun 0 (by omega)
  simp only [Nat.cast_zero, zero_add] at hk hm hj
  have hBm : mkPt L 0 ∈ D.target.carrier := by
    rw [← hX0, ← hk]; exact Erdos634.MarchInduction.pts_mem_target D.toDissection t1 k
  have hYm : lpT (u : ℝ) (v : ℝ) (-1) (f W.length * L) 0 1 ∈ D.target.carrier := by
    rw [← hj]; exact Erdos634.MarchInduction.pts_mem_target D.toDissection t1 j
  have hYpt : lpT (u : ℝ) (v : ℝ) (-1) (f W.length * L) 0 1 =
      mkPt (L - ((u : ℝ) * v - uuT (u : ℝ) (v : ℝ))) (hhT (u : ℝ) (v : ℝ)) := by
    rw [hx]; unfold lpT; exact mkPt_congr (by ring) (by ring)
  have hY1 : 0 < (lpT (u : ℝ) (v : ℝ) (-1) (f W.length * L) 0 1) 1 := by
    rw [lpT_snd]; have := hhT_pos hu huv hv2; linarith
  have hint1 : openSegment ℝ (mkPt L 0) (lpT (u : ℝ) (v : ℝ) (-1) (f W.length * L) 0 1) ⊆
      interior D.target.carrier := by
    refine S.interior_seg hBm hYm (Or.inr hY1) (Or.inl ?_) (Or.inr ?_)
    · rw [gA_mk]; nlinarith [S.hay]
    · rw [hYpt, gB_mk]; nlinarith
  have htot : ∑ i, (D.tile i).localAngle (lpT (u : ℝ) (v : ℝ) (-1) (f W.length * L) 0 0) = Real.pi - 2 * α := by
    rw [hX0]
    have h0 : (mkPt L 0 : Plane) = D.toDissection.target.pts 1 := ((target_pts01 S).2.1).symm
    rw [h0, vertex_total D.toDissection 1]
    exact hapex
  have hα1 : (D.tile t1).localAngle (lpT (u : ℝ) (v : ℝ) (-1) (f W.length * L) 0 0) = α := by
    have hU : HasV D t1 (lpT (u : ℝ) (v : ℝ) (-1) (f W.length * L) 0 0)
        (lpT (u : ℝ) (v : ℝ) (-1) (f W.length * L) 1 0) (lpT (u : ℝ) (v : ℝ) (-1) (f W.length * L) 0 1) :=
      ⟨k, m, j, hkm, hkj, hmj, hk, hm, hj⟩
    exact (U_anglesT hu huv hv2 hε S.tile.hab S.tile.ac S.tile.bc S.hM (by simpa using hU)).1
  have hint : openSegment ℝ (lpT (u : ℝ) (v : ℝ) (-1) (f W.length * L) 0 0)
      (lpT (u : ℝ) (v : ℝ) (-1) (f W.length * L) 0 1) ⊆ interior D.target.carrier := by
    rw [hX0]; exact hint1
  obtain ⟨hRay, -⟩ := apex_ray_tile S (X0 := lpT (u : ℝ) (v : ℝ) (-1) (f W.length * L) 0 0) (fun p : Plane => p 1)
    phi_y_lineMap (fun q hq => (S.mem hq).1) (by rw [hX0]; rfl) hY1 hint htot (t1 := t1) (k := k) (m := j) (j := m)
    hkj hkm (Ne.symm hmj) hk hj hα1
  have hch : ∀ j : ℕ, 1 ≤ j → lpT (u : ℝ) (v : ℝ) (-1) (f W.length * L) 0 (j : ℝ) ∈ D.target.carrier →
      openSegment ℝ (lpT (u : ℝ) (v : ℝ) (-1) (f W.length * L) 0 0)
        (lpT (u : ℝ) (v : ℝ) (-1) (f W.length * L) 0 (j : ℝ)) ⊆ interior D.target.carrier := by
    intro j hj hjm
    rw [hX0]
    have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
    refine S.interior_seg hBm hjm (Or.inr ?_) (Or.inl ?_) (Or.inr ?_)
    · rw [lpT_snd]; have := hhT_pos hu huv hv2; nlinarith
    · rw [gA_mk]; nlinarith [S.hay]
    · have : lpT (u : ℝ) (v : ℝ) (-1) (f W.length * L) 0 (j : ℝ) =
          mkPt (L - (j : ℝ) * ((u : ℝ) * v - uuT (u : ℝ) (v : ℝ))) ((j : ℝ) * hhT (u : ℝ) (v : ℝ)) := by
        rw [hx]; unfold lpT; exact mkPt_congr (by ring) rfl
      rw [this, gB_mk]
      nlinarith
  rw [hm] at hRay
  exact lemma33_interior C hn1 hnu hrun hch (hT0_of_ray C hRay) hVnv hnoγ hst

#print axioms apex_end

end Erdos634.Draft.ThmDRun
