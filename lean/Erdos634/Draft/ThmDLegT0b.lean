import Mathlib.Tactic
import Erdos634.Draft.ThmDLegT0

/-!
Credit: the method (rigidity window, Lemmas 30-34, row induction, Theorem 37) is adapted from M. Beeson and G. Rosu, 'Tiling a triangle into a prime number of congruent triangles' (preprint, 16 Oct 2026); the transfer to the tile with gamma = 2 alpha (fan lemma at straight points, windows u and v, Lemma K) is ours.

# Theorem D' (ThmDGeo, item (4)/(5)): `T₀` at the interior starts of a positioned leg  

`T0_stop_cp` : an interior `γ`-stop (the edge before the `c>` block ends with `γ`) gives a `RayTileAC` across the ray of the first tile;
`T0_stop_cm` the mirror.  Frame helpers: `seg_int_base`, `base_between`, `phi_y_lineMap`.
-/

namespace Erdos634.Draft.ThmDRun

open Erdos634.Geometry Erdos634.CertCoord Erdos634.Draft.SideRun Erdos634.Draft.APrimeLegBuild
  Erdos634.Draft.APrimeSeat1 Erdos634.Draft.APrimeLeg Erdos634.MarchSlots Set

variable {N : ℕ} {D : CongruentDissection N} {u v : ℕ} {α β γ L ax ay ε x : ℝ}

theorem phi_y_lineMap (p q : Plane) (t : ℝ) :
    (AffineMap.lineMap p q t : Plane) 1 = p 1 + t * (q 1 - p 1) := by
  simp [AffineMap.lineMap_apply]; ring

theorem base_between {p q r : ℝ} (hpq : p < q) (hqr : q < r) :
    mkPt q 0 ∈ openSegment ℝ (mkPt r 0) (mkPt p 0) := by
  rw [openSegment_eq_image_lineMap]
  refine ⟨(r - q) / (r - p), ⟨div_pos (by linarith) (by linarith), ?_⟩, ?_⟩
  · rw [div_lt_one (by linarith)]; linarith
  · rw [Erdos634.RunPartition.CSlot.lineMap_mkPt]
    refine mkPt_congr ?_ (by ring)
    have : r - p ≠ 0 := by linarith
    field_simp; ring

theorem seg_int_base (S : SetupT D u v α β γ L ax ay) {x : ℝ} (hx0 : 0 < x) (hxL : x < L)
    (hXm : mkPt x 0 ∈ D.target.carrier) {Z : Plane} (hZ : Z ∈ D.target.carrier) (hZ1 : 0 < Z 1) :
    openSegment ℝ (mkPt x 0) Z ⊆ interior D.target.carrier := by
  refine S.interior_seg hXm hZ (Or.inr hZ1) (Or.inl ?_) (Or.inl ?_)
  · rw [gA_mk]; nlinarith [S.hay]
  · rw [gB_mk]; nlinarith [S.hay]

theorem T0_stop_cp (S : SetupT D u v α β γ L ax ay) {W : List OE} {f : ℕ → ℝ} (hB : Brk S W f) {a : ℕ}
    (ha1 : 1 ≤ a) (haw : a < W.length) (hcp0 : W[a]? = some OE.cp)
    (hpre : ∃ o, W[a - 1]? = some o ∧ o.r = Ang.ga) :
    ∃ t1 : Fin N, RayTileAC D u v (lpT (u : ℝ) (v : ℝ) 1 (f a * L) 0 0) (lpT (u : ℝ) (v : ℝ) 1 (f a * L) 0 1)
      (lpT (u : ℝ) (v : ℝ) 1 (f a * L) 1 0) t1 := by
  have hu := S.u0
  have huv := S.uv'
  have hv2 := S.v2
  have hL := S.hL
  have hc := S.c_pos
  have hε : (1 : ℝ) ^ 2 = 1 := by norm_num
  obtain ⟨hpos, hrun⟩ := blk_cp S hB (a := a) (n := 1) (by omega) (fun j hj => by
    have : j = 0 := by omega
    subst this; simpa using hcp0)
  obtain ⟨t1, k, m, j, hkm, hkj, hmj, hk, hm, hj⟩ := hrun 0 (by norm_num)
  simp only [Nat.cast_zero, zero_add] at hk hm hj
  have hX0 : lpT (u : ℝ) (v : ℝ) 1 (f a * L) 0 0 = mkPt (f a * L) 0 := by
    rw [lpT_base]; exact mkPt_congr (by ring) rfl
  have hfa0 : 0 < f a := by
    have := hB.lt_of_lt (i := 0) (j := a) (by omega) (by omega)
    rwa [hB.f0] at this
  have hfa1 : f a < 1 := by
    have h1 := hB.lt_succ haw
    have h2 := hB.le_one (i := a + 1) (by omega)
    linarith
  have hx0 : 0 < f a * L := mul_pos hfa0 hL
  have hxL : f a * L < L := by nlinarith
  have hXm : mkPt (f a * L) 0 ∈ D.target.carrier := by
    rw [← hX0, ← hk]; exact Erdos634.MarchInduction.pts_mem_target D.toDissection t1 k
  have hYm : lpT (u : ℝ) (v : ℝ) 1 (f a * L) 0 1 ∈ D.target.carrier := by
    rw [← hj]; exact Erdos634.MarchInduction.pts_mem_target D.toDissection t1 j
  have hY1 : 0 < (lpT (u : ℝ) (v : ℝ) 1 (f a * L) 0 1) 1 := by
    rw [lpT_snd]; have := hhT_pos hu huv hv2; linarith
  -- the previous tile
  obtain ⟨o, ho, hor⟩ := hpre
  have hlt : a - 1 < W.length := by omega
  have hgeto : W[a - 1]'hlt = o := by
    rw [List.getElem?_eq_getElem hlt] at ho
    exact Option.some.inj ho
  obtain ⟨t2, j2, k2, hjk2, hj2, hk2, hj2ang, hk2ang, hw2⟩ := hB.step (a - 1) hlt
  rw [hgeto] at hk2ang
  have e1 : a - 1 + 1 = a := by omega
  rw [e1] at hk2 hw2
  have hγ2 : (D.tile t2).localAngle (lpT (u : ℝ) (v : ℝ) 1 (f a * L) 0 0) = γ := by
    rw [hX0, ← hk2, hk2ang, hor, S.hγ]; simp [angVal]
  have hα1 : (D.tile t1).localAngle (lpT (u : ℝ) (v : ℝ) 1 (f a * L) 0 0) = α := by
    have hU : HasV D t1 (lpT (u : ℝ) (v : ℝ) 1 (f a * L) 0 0) (lpT (u : ℝ) (v : ℝ) 1 (f a * L) 1 0)
        (lpT (u : ℝ) (v : ℝ) 1 (f a * L) 0 1) := ⟨k, m, j, hkm, hkj, hmj, hk, hm, hj⟩
    exact (U_anglesT hu huv hv2 hε S.tile.hab S.tile.ac S.tile.bc S.hM
      (by simpa using hU)).1
  have hfpred : f (a - 1) < f a := by
    have := hB.lt_succ hlt
    rwa [e1] at this
  have hWZ : lpT (u : ℝ) (v : ℝ) 1 (f a * L) 0 0 ∈ openSegment ℝ ((D.tile t1).pts m) ((D.tile t2).pts j2) := by
    rw [hm, hj2, hX0, lpT_base]
    have := base_between (p := f (a - 1) * L) (q := f a * L) (r := f a * L + 1 * (1 * ((u : ℝ) * v)))
      (by nlinarith) (by nlinarith)
    exact this
  have hint : openSegment ℝ (lpT (u : ℝ) (v : ℝ) 1 (f a * L) 0 0) (lpT (u : ℝ) (v : ℝ) 1 (f a * L) 0 1) ⊆
      interior D.target.carrier := by
    rw [hX0]; exact seg_int_base S hx0 hxL hXm hYm hY1
  have hX : lpT (u : ℝ) (v : ℝ) 1 (f a * L) 0 0 ∈ frontier D.target.carrier := by
    rw [hX0]; exact S.frontier_y0 hXm rfl
  have hXv : lpT (u : ℝ) (v : ℝ) 1 (f a * L) 0 0 ∉ Set.range D.target.pts := by
    rw [hX0]; exact base_vertex_not S hx0 hxL
  obtain ⟨hRay, -⟩ := stop_ray_tile S hX hXv (fun p : Plane => p 1) phi_y_lineMap
    (fun q hq => (S.mem hq).1) (by rw [hX0]; rfl) hY1 hint (t1 := t1) (t2 := t2) (k := k) (m := j) (j := m)
    hkj hkm (Ne.symm hmj) hk hj hα1 (Z := (D.tile t2).pts j2) (k2 := j2) rfl hWZ hγ2
  exact ⟨t1, by rw [← hm]; exact hRay⟩

#print axioms T0_stop_cp

theorem T0_stop_cm (S : SetupT D u v α β γ L ax ay) {W : List OE} {f : ℕ → ℝ} (hB : Brk S W f) {b : ℕ}
    (hb1 : 1 ≤ b) (hbw : b < W.length) (hcm0 : W[b - 1]? = some OE.cm)
    (hnext : ∃ o, W[b]? = some o ∧ o.l = Ang.ga) :
    ∃ t1 : Fin N, RayTileAC D u v (lpT (u : ℝ) (v : ℝ) (-1) (f b * L) 0 0) (lpT (u : ℝ) (v : ℝ) (-1) (f b * L) 0 1)
      (lpT (u : ℝ) (v : ℝ) (-1) (f b * L) 1 0) t1 := by
  have hu := S.u0
  have huv := S.uv'
  have hv2 := S.v2
  have hL := S.hL
  have hc := S.c_pos
  have hε : (-1 : ℝ) ^ 2 = 1 := by norm_num
  obtain ⟨hpos, hrun⟩ := blk_cm S hB (b := b) (n := 1) (by omega) hb1 (fun j hj => by
    have : j = 0 := by omega
    subst this; simpa using hcm0)
  obtain ⟨t1, k, m, j, hkm, hkj, hmj, hk, hm, hj⟩ := hrun 0 (by norm_num)
  simp only [Nat.cast_zero, zero_add] at hk hm hj
  have hX0 : lpT (u : ℝ) (v : ℝ) (-1) (f b * L) 0 0 = mkPt (f b * L) 0 := by
    rw [lpT_base]; exact mkPt_congr (by ring) rfl
  have hfb0 : 0 < f b := by
    have := hB.lt_of_lt (i := 0) (j := b) (by omega) (by omega)
    rwa [hB.f0] at this
  have hfb1 : f b < 1 := by
    have h1 := hB.lt_succ hbw
    have h2 := hB.le_one (i := b + 1) (by omega)
    linarith
  have hx0 : 0 < f b * L := mul_pos hfb0 hL
  have hxL : f b * L < L := by nlinarith
  have hXm : mkPt (f b * L) 0 ∈ D.target.carrier := by
    rw [← hX0, ← hk]; exact Erdos634.MarchInduction.pts_mem_target D.toDissection t1 k
  have hYm : lpT (u : ℝ) (v : ℝ) (-1) (f b * L) 0 1 ∈ D.target.carrier := by
    rw [← hj]; exact Erdos634.MarchInduction.pts_mem_target D.toDissection t1 j
  have hY1 : 0 < (lpT (u : ℝ) (v : ℝ) (-1) (f b * L) 0 1) 1 := by
    rw [lpT_snd]; have := hhT_pos hu huv hv2; linarith
  -- the next tile
  obtain ⟨o, ho, hol⟩ := hnext
  have hgeto : W[b]'hbw = o := by
    rw [List.getElem?_eq_getElem hbw] at ho
    exact Option.some.inj ho
  obtain ⟨t2, j2, k2, hjk2, hj2, hk2, hj2ang, hk2ang, hw2⟩ := hB.step b hbw
  rw [hgeto] at hj2ang
  have hγ2 : (D.tile t2).localAngle (lpT (u : ℝ) (v : ℝ) (-1) (f b * L) 0 0) = γ := by
    rw [hX0, ← hj2, hj2ang, hol, S.hγ]; simp [angVal]
  have hα1 : (D.tile t1).localAngle (lpT (u : ℝ) (v : ℝ) (-1) (f b * L) 0 0) = α := by
    have hU : HasV D t1 (lpT (u : ℝ) (v : ℝ) (-1) (f b * L) 0 0) (lpT (u : ℝ) (v : ℝ) (-1) (f b * L) 1 0)
        (lpT (u : ℝ) (v : ℝ) (-1) (f b * L) 0 1) := ⟨k, m, j, hkm, hkj, hmj, hk, hm, hj⟩
    exact (U_anglesT hu huv hv2 hε S.tile.hab S.tile.ac S.tile.bc S.hM
      (by simpa using hU)).1
  have hfsucc : f b < f (b + 1) := hB.lt_succ hbw
  have hWZ : lpT (u : ℝ) (v : ℝ) (-1) (f b * L) 0 0 ∈ openSegment ℝ ((D.tile t1).pts m) ((D.tile t2).pts k2) := by
    rw [hm, hk2, hX0, lpT_base, openSegment_symm]
    have := base_between (p := f b * L + (-1) * (1 * ((u : ℝ) * v))) (q := f b * L) (r := f (b + 1) * L)
      (by nlinarith) (by nlinarith)
    exact this
  have hint : openSegment ℝ (lpT (u : ℝ) (v : ℝ) (-1) (f b * L) 0 0) (lpT (u : ℝ) (v : ℝ) (-1) (f b * L) 0 1) ⊆
      interior D.target.carrier := by
    rw [hX0]; exact seg_int_base S hx0 hxL hXm hYm hY1
  have hX : lpT (u : ℝ) (v : ℝ) (-1) (f b * L) 0 0 ∈ frontier D.target.carrier := by
    rw [hX0]; exact S.frontier_y0 hXm rfl
  have hXv : lpT (u : ℝ) (v : ℝ) (-1) (f b * L) 0 0 ∉ Set.range D.target.pts := by
    rw [hX0]; exact base_vertex_not S hx0 hxL
  obtain ⟨hRay, -⟩ := stop_ray_tile S hX hXv (fun p : Plane => p 1) phi_y_lineMap
    (fun q hq => (S.mem hq).1) (by rw [hX0]; rfl) hY1 hint (t1 := t1) (t2 := t2) (k := k) (m := j) (j := m)
    hkj hkm (Ne.symm hmj) hk hj hα1 (Z := (D.tile t2).pts k2) (k2 := k2) rfl hWZ hγ2
  exact ⟨t1, by rw [← hm]; exact hRay⟩

#print axioms T0_stop_cm
/-- the `α | α` junction of `cm` and `cp` at the index `a`: `T₀` across the ray of the east tile or of the west tile -/
theorem T0_aa (S : SetupT D u v α β γ L ax ay) {W : List OE} {f : ℕ → ℝ} (hB : Brk S W f) {a : ℕ}
    (ha1 : 1 ≤ a) (haw : a < W.length) (hcp0 : W[a]? = some OE.cp) (hcm0 : W[a - 1]? = some OE.cm) :
    (∃ t1 : Fin N, RayTileAC D u v (lpT (u : ℝ) (v : ℝ) 1 (f a * L) 0 0) (lpT (u : ℝ) (v : ℝ) 1 (f a * L) 0 1)
      (lpT (u : ℝ) (v : ℝ) 1 (f a * L) 1 0) t1) ∨
    (∃ t2 : Fin N, RayTileAC D u v (lpT (u : ℝ) (v : ℝ) (-1) (f a * L) 0 0) (lpT (u : ℝ) (v : ℝ) (-1) (f a * L) 0 1)
      (lpT (u : ℝ) (v : ℝ) (-1) (f a * L) 1 0) t2) := by
  have hu := S.u0
  have huv := S.uv'
  have hv2 := S.v2
  have hL := S.hL
  have hc := S.c_pos
  have hε1 : (1 : ℝ) ^ 2 = 1 := by norm_num
  have hε2 : (-1 : ℝ) ^ 2 = 1 := by norm_num
  obtain ⟨-, hrun1⟩ := blk_cp S hB (a := a) (n := 1) (by omega) (fun j hj => by
    have : j = 0 := by omega
    subst this; simpa using hcp0)
  obtain ⟨-, hrun2⟩ := blk_cm S hB (b := a) (n := 1) (by omega) ha1 (fun j hj => by
    have : j = 0 := by omega
    subst this; simpa using hcm0)
  obtain ⟨t1, k, m, j, hkm, hkj, hmj, hk, hm, hj⟩ := hrun1 0 (by norm_num)
  obtain ⟨t2, k₂, m₂, j₂, hkm₂, hkj₂, hmj₂, hk₂, hm₂, hj₂⟩ := hrun2 0 (by norm_num)
  simp only [Nat.cast_zero, zero_add] at hk hm hj hk₂ hm₂ hj₂
  have hX1 : lpT (u : ℝ) (v : ℝ) 1 (f a * L) 0 0 = mkPt (f a * L) 0 := by
    rw [lpT_base]; exact mkPt_congr (by ring) rfl
  have hX2 : lpT (u : ℝ) (v : ℝ) (-1) (f a * L) 0 0 = mkPt (f a * L) 0 := by
    rw [lpT_base]; exact mkPt_congr (by ring) rfl
  have hfa0 : 0 < f a := by
    have := hB.lt_of_lt (i := 0) (j := a) (by omega) (by omega)
    rwa [hB.f0] at this
  have hfa1 : f a < 1 := by
    have h1 := hB.lt_succ haw
    have h2 := hB.le_one (i := a + 1) (by omega)
    linarith
  have hx0 : 0 < f a * L := mul_pos hfa0 hL
  have hxL : f a * L < L := by nlinarith
  have hXm : mkPt (f a * L) 0 ∈ D.target.carrier := by
    rw [← hX1, ← hk]; exact Erdos634.MarchInduction.pts_mem_target D.toDissection t1 k
  have hY1m : lpT (u : ℝ) (v : ℝ) 1 (f a * L) 0 1 ∈ D.target.carrier := by
    rw [← hj]; exact Erdos634.MarchInduction.pts_mem_target D.toDissection t1 j
  have hY2m : lpT (u : ℝ) (v : ℝ) (-1) (f a * L) 0 1 ∈ D.target.carrier := by
    rw [← hj₂]; exact Erdos634.MarchInduction.pts_mem_target D.toDissection t2 j₂
  have hY1 : 0 < (lpT (u : ℝ) (v : ℝ) 1 (f a * L) 0 1) 1 := by
    rw [lpT_snd]; have := hhT_pos hu huv hv2; linarith
  have hY2 : 0 < (lpT (u : ℝ) (v : ℝ) (-1) (f a * L) 0 1) 1 := by
    rw [lpT_snd]; have := hhT_pos hu huv hv2; linarith
  have hα1 : (D.tile t1).localAngle (mkPt (f a * L) 0) = α := by
    have hU : HasV D t1 (lpT (u : ℝ) (v : ℝ) 1 (f a * L) 0 0) (lpT (u : ℝ) (v : ℝ) 1 (f a * L) 1 0)
        (lpT (u : ℝ) (v : ℝ) 1 (f a * L) 0 1) := ⟨k, m, j, hkm, hkj, hmj, hk, hm, hj⟩
    rw [← hX1]
    exact (U_anglesT hu huv hv2 hε1 S.tile.hab S.tile.ac S.tile.bc S.hM (by simpa using hU)).1
  have hα2 : (D.tile t2).localAngle (mkPt (f a * L) 0) = α := by
    have hU : HasV D t2 (lpT (u : ℝ) (v : ℝ) (-1) (f a * L) 0 0) (lpT (u : ℝ) (v : ℝ) (-1) (f a * L) 1 0)
        (lpT (u : ℝ) (v : ℝ) (-1) (f a * L) 0 1) := ⟨k₂, m₂, j₂, hkm₂, hkj₂, hmj₂, hk₂, hm₂, hj₂⟩
    rw [← hX2]
    exact (U_anglesT hu huv hv2 hε2 S.tile.hab S.tile.ac S.tile.bc S.hM (by simpa using hU)).1
  have hWZ : mkPt (f a * L) 0 ∈ openSegment ℝ ((D.tile t1).pts m) ((D.tile t2).pts m₂) := by
    rw [hm, hm₂, lpT_base, lpT_base]
    have := base_between (p := f a * L + (-1) * (1 * ((u : ℝ) * v))) (q := f a * L)
      (r := f a * L + 1 * (1 * ((u : ℝ) * v))) (by nlinarith) (by nlinarith)
    exact this
  have hint1 : openSegment ℝ (mkPt (f a * L) 0) (lpT (u : ℝ) (v : ℝ) 1 (f a * L) 0 1) ⊆
      interior D.target.carrier := seg_int_base S hx0 hxL hXm hY1m hY1
  have hint2 : openSegment ℝ (mkPt (f a * L) 0) (lpT (u : ℝ) (v : ℝ) (-1) (f a * L) 0 1) ⊆
      interior D.target.carrier := seg_int_base S hx0 hxL hXm hY2m hY2
  have hX : mkPt (f a * L) 0 ∈ frontier D.target.carrier := S.frontier_y0 hXm rfl
  have hXv : mkPt (f a * L) 0 ∉ Set.range D.target.pts := base_vertex_not S hx0 hxL
  rcases alphaalpha_ray_tile S hX hXv (fun p : Plane => p 1) phi_y_lineMap (fun q hq => (S.mem hq).1) rfl hY1 hY2
    hint1 hint2 (t1 := t1) (t2 := t2) (k := k) (m := j) (j := m) (k₂ := k₂) (m₂ := j₂) (j₂ := m₂)
    hkj hkm (Ne.symm hmj) hkj₂ hkm₂ (Ne.symm hmj₂) (by rw [hk, hX1]) hj (by rw [hk₂, hX2]) hj₂ hα1 hα2 hWZ with h | h
  · left
    refine ⟨t1, ?_⟩
    rw [hX1]
    rw [← hm]; exact h
  · right
    refine ⟨t2, ?_⟩
    rw [hX2]
    rw [← hm₂]; exact h

#print axioms T0_aa

end Erdos634.Draft.ThmDRun
