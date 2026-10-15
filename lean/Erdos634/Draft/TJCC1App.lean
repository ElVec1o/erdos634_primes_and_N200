-- No sorry, no native_decide.
-- Applications of the five pointwise lemmas to the real 8-tile 30-60-90 tiling C1 at points of the T-junction
-- edge (4,0)-(6,2) (lattice; real (4,0)-(6,2*sqrt 3)): tiles 2,3 (vertex (5,1)) on one side, tile 6 (open edge) on the other.
import Erdos634.Draft.TJCC1

namespace Erdos634.Draft.TJCC1App

open Erdos634.Geometry Erdos634.CertCoord Erdos634.Draft.TJCHelp Erdos634.Draft.G3CCert
  Erdos634.Draft.G3RCCommon Erdos634.Draft.G3RC1Tiling Erdos634.Draft.TJCC1

/-- the T-junction test point (9/2, 1/2) in lattice coordinates -/
noncomputable def X : Plane := mkPt (9/2) (Real.sqrt 3 / 2)

theorem mem_edge_of (T : Tri) (k : Fin 3) {a b x : Plane} (ha : T.pts k = a) (hb : T.pts (k + 1) = b)
    (h : x ∈ segment ℝ a b) : x ∈ T.edge k := by
  unfold Tri.edge; rw [ha, hb]; exact h

theorem seg_lat (p q : ℤ × ℤ) (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    mkPt ((1 - t) * (p.1 : ℝ) + t * q.1) (((1 - t) * (p.2 : ℝ) + t * q.2) * Real.sqrt 3) ∈
      segment ℝ (mkPt (p.1 : ℝ) ((p.2 : ℝ) * Real.sqrt 3)) (mkPt (q.1 : ℝ) ((q.2 : ℝ) * Real.sqrt 3)) := by
  have := mkPt_mem_segment (p.1 : ℝ) ((p.2 : ℝ) * Real.sqrt 3) (q.1 : ℝ) ((q.2 : ℝ) * Real.sqrt 3) t h0 h1
  convert this using 2
  ring

theorem pt_toPt (i : Fin cert.leaves.length) (k : Fin 3) (p : LP) (hv : vtx (cert.leaves.get i) k = p) :
    (D.tile i).pts k = toPt p := by rw [tile_pts_gen, hv]

theorem X_seg (p q : LP) (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1)
    (hx : (1 - t) * (p.1 : ℝ) + t * q.1 = 9 / 2) (hy : (1 - t) * (p.2 : ℝ) + t * q.2 = 1 / 2) :
    X ∈ segment ℝ (toPt p) (toPt q) := by
  have := seg_lat p q t h0 h1
  rw [hx, hy] at this
  have e : X = mkPt (9 / 2) (1 / 2 * Real.sqrt 3) := by
    unfold X; congr 1; ring
  rw [e]; exact this

theorem X_ne_toPt (p : LP) : X ≠ toPt p := by
  intro h
  have h1 := (mkPt_inj h).1
  have h2 : (((2 * p.1 : ℤ)) : ℝ) = ((9 : ℤ) : ℝ) := by push_cast; unfold rx at h1; linarith
  have h3 : 2 * p.1 = 9 := by exact_mod_cast h2
  omega

theorem X_ne_pts (i : Fin cert.leaves.length) (k : Fin 3) : X ≠ (D.tile i).pts k := by
  rw [tile_pts_gen]; exact X_ne_toPt _

theorem X_not_vertex : X ∉ D.vertexSet := by
  intro hmem
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hmem
  obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hi
  exact X_ne_pts i k (by simpa using hk)

theorem ld_val (i : Fin cert.leaves.length) (k : Fin 3) (p q : LP)
    (hp : vtx (cert.leaves.get i) k = p) (hq : vtx (cert.leaves.get i) (k + 1) = q) :
    (D.tile i).leftDir k = mkPt ((q.1 : ℝ) - p.1) (((q.2 : ℝ) - p.2) * Real.sqrt 3) := by
  rw [D_leftDir, hp, hq, toPt_eq, toPt_eq, mkPt_sub]
  congr 1; ring

/-! ## the functional `f = √3 u - v'` : on a lattice point `(u,v)` it is `√3 (u - v)`; the T-junction line is `u - v = 4` -/

noncomputable abbrev fL : Plane →ₗ[ℝ] ℝ := lin (Real.sqrt 3) (-1)

theorem fL_toPt (p : LP) : fL (toPt p) = Real.sqrt 3 * ((p.1 : ℝ) - p.2) := by
  rw [lin_toPt]; ring

theorem fL_ne : fL ≠ 0 := lin_ne_zero (Or.inr (by norm_num))

theorem side_le (i : Fin cert.leaves.length)
    (h : ∀ k, (vtx (cert.leaves.get i) k).1 - (vtx (cert.leaves.get i) k).2 ≤ 4) :
    ∀ k, fL ((D.tile i).pts k) ≤ 4 * Real.sqrt 3 := by
  intro k
  rw [tile_pts_gen, fL_toPt]
  have : (((vtx (cert.leaves.get i) k).1 : ℝ) - (vtx (cert.leaves.get i) k).2) ≤ 4 := by exact_mod_cast h k
  nlinarith [s3pos]

theorem side_ge (i : Fin cert.leaves.length)
    (h : ∀ k, 4 ≤ (vtx (cert.leaves.get i) k).1 - (vtx (cert.leaves.get i) k).2) :
    ∀ k, 4 * Real.sqrt 3 ≤ fL ((D.tile i).pts k) := by
  intro k
  rw [tile_pts_gen, fL_toPt]
  have : (4 : ℝ) ≤ (((vtx (cert.leaves.get i) k).1 : ℝ) - (vtx (cert.leaves.get i) k).2) := by exact_mod_cast h k
  nlinarith [s3pos]

theorem side_eq (i : Fin cert.leaves.length) (k : Fin 3)
    (h : (vtx (cert.leaves.get i) k).1 - (vtx (cert.leaves.get i) k).2 = 4) :
    fL ((D.tile i).pts k) = 4 * Real.sqrt 3 := by
  rw [tile_pts_gen, fL_toPt]
  have : (((vtx (cert.leaves.get i) k).1 : ℝ) - (vtx (cert.leaves.get i) k).2) = 4 := by exact_mod_cast h
  rw [this]; ring

/-! ## (1) `leftDir_antiparallel` at the T-junction point X: tile 2 (edge (4,0)-(5,1)) against tile 6 (edge (6,2)-(4,0)) -/

theorem X_in_tile2_edge1 : X ∈ (D.tile (tl 2)).edge 1 :=
  mem_edge_of _ 1 (pt_toPt _ _ (4, 0) (by decide +kernel)) (pt_toPt _ _ (5, 1) (by decide +kernel))
    (X_seg (4, 0) (5, 1) (1/2) (by norm_num) (by norm_num) (by norm_num) (by norm_num))

theorem X_in_tile6_edge2 : X ∈ (D.tile (tl 6)).edge 2 :=
  mem_edge_of _ 2 (pt_toPt _ _ (6, 2) (by decide +kernel)) (pt_toPt _ _ (4, 0) (by decide +kernel))
    (X_seg (6, 2) (4, 0) (3/4) (by norm_num) (by norm_num) (by norm_num) (by norm_num))

theorem c1_antiparallel :
    ∃ c : ℝ, c < 0 ∧ (D.tile (tl 6)).leftDir 2 = c • (D.tile (tl 2)).leftDir 1 ∧ c = -2 ∧
      (D.tile (tl 2)).leftDir 1 = mkPt 1 (Real.sqrt 3) ∧
      (D.tile (tl 6)).leftDir 2 = mkPt (-2) (-2 * Real.sqrt 3) := by
  obtain ⟨hz2, hp2⟩ := (D.tile (tl 2)).onEdge_param X_in_tile2_edge1 (X_ne_pts _ _) (X_ne_pts _ _)
  obtain ⟨hz6, hp6⟩ := (D.tile (tl 6)).onEdge_param X_in_tile6_edge2 (X_ne_pts _ _) (X_ne_pts _ _)
  have hne : tl 2 ≠ tl 6 := by decide
  obtain ⟨c, hc, h⟩ := D.leftDir_antiparallel hne hz2 hp2 hz6 hp6
  have h' : (D.tile (tl 6)).leftDir 2 = c • (D.tile (tl 2)).leftDir 1 := h
  have h2 : (D.tile (tl 2)).leftDir 1 = mkPt 1 (Real.sqrt 3) := by
    rw [ld_val _ _ (4, 0) (5, 1) (by decide +kernel) (by decide +kernel)]
    congr 1 <;> push_cast <;> ring
  have h6 : (D.tile (tl 6)).leftDir 2 = mkPt (-2) (-2 * Real.sqrt 3) := by
    rw [ld_val _ _ (6, 2) (4, 0) (by decide +kernel) (by decide +kernel)]
    congr 1 <;> push_cast <;> ring
  refine ⟨c, hc, h', ?_, h2, h6⟩
  rw [h2, h6, mkPt_smul] at h'
  have := (mkPt_inj h').1
  linarith


theorem mem_seg_toPt (p q r : LP) (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1)
    (hx : (1 - t) * (p.1 : ℝ) + t * q.1 = r.1) (hy : (1 - t) * (p.2 : ℝ) + t * q.2 = r.2) :
    toPt r ∈ segment ℝ (toPt p) (toPt q) := by
  have := seg_lat p q t h0 h1
  rw [hx, hy] at this
  exact this

theorem X_oseg (p q : LP) (t : ℝ) (h0 : 0 < t) (h1 : t < 1)
    (hx : (1 - t) * (p.1 : ℝ) + t * q.1 = 9 / 2) (hy : (1 - t) * (p.2 : ℝ) + t * q.2 = 1 / 2) :
    X ∈ openSegment ℝ (toPt p) (toPt q) := by
  have := mkPt_mem_openSegment (p.1 : ℝ) ((p.2 : ℝ) * Real.sqrt 3) (q.1 : ℝ) ((q.2 : ℝ) * Real.sqrt 3) t h0 h1
  have e : X = mkPt ((1 - t) * (p.1 : ℝ) + t * q.1) ((1 - t) * ((p.2 : ℝ) * Real.sqrt 3) + t * ((q.2 : ℝ) * Real.sqrt 3)) := by
    unfold X; rw [hx]; congr 1
    have : (1 - t) * ((p.2 : ℝ) * Real.sqrt 3) + t * ((q.2 : ℝ) * Real.sqrt 3)
        = ((1 - t) * (p.2 : ℝ) + t * q.2) * Real.sqrt 3 := by ring
    rw [this, hy]; ring
  rw [e]; exact this

/-! ## (3) `sameside_edges_subsingleton`: tile 2 edge (4,0)-(5,1) and tile 3 edge (5,1)-(6,2), both on the T-junction line
`u - v = 4`, both in `{f ≤ c}`; they meet exactly in the T-vertex (5,1) -/

theorem c1_sameside :
    ((D.tile (tl 2)).edge 1 ∩ (D.tile (tl 3)).edge 1).Subsingleton ∧
    toPt (5, 1) ∈ (D.tile (tl 2)).edge 1 ∩ (D.tile (tl 3)).edge 1 := by
  have hne : ((tl 2 : Fin cert.leaves.length), (1 : Fin 3)) ≠ ((tl 3 : Fin cert.leaves.length), (1 : Fin 3)) := by decide
  have hle₁ := carrier_le (D.tile (tl 2)) (f := fL) (c := 4 * Real.sqrt 3) (side_le _ (by decide +kernel))
  have hle₂ := carrier_le (D.tile (tl 3)) (f := fL) (c := 4 * Real.sqrt 3) (side_le _ (by decide +kernel))
  have a2 : (D.tile (tl 2)).pts 1 = toPt (4, 0) := pt_toPt _ _ _ (by decide +kernel)
  have b2 : (D.tile (tl 2)).pts (1 + 1) = toPt (5, 1) := pt_toPt _ _ _ (by decide +kernel)
  have a3 : (D.tile (tl 3)).pts 1 = toPt (5, 1) := pt_toPt _ _ _ (by decide +kernel)
  have b3 : (D.tile (tl 3)).pts (1 + 1) = toPt (6, 2) := pt_toPt _ _ _ (by decide +kernel)
  have hE₁ : ∀ y ∈ (D.tile (tl 2)).edge 1, fL y = 4 * Real.sqrt 3 := by
    intro y hy
    unfold Tri.edge at hy; rw [a2, b2] at hy
    exact seg_eq (by rw [fL_toPt]; push_cast; ring) (by rw [fL_toPt]; push_cast; ring) hy
  have hE₂ : ∀ y ∈ (D.tile (tl 3)).edge 1, fL y = 4 * Real.sqrt 3 := by
    intro y hy
    unfold Tri.edge at hy; rw [a3, b3] at hy
    exact seg_eq (by rw [fL_toPt]; push_cast; ring) (by rw [fL_toPt]; push_cast; ring) hy
  have hsub := D.sameside_edges_subsingleton fL (4 * Real.sqrt 3) fL_ne hne hle₁ hle₂ hE₁ hE₂
  refine ⟨hsub, ?_, ?_⟩
  · exact mem_edge_of _ 1 a2 b2 (right_mem_segment ℝ _ _)
  · exact mem_edge_of _ 1 a3 b3 (left_mem_segment ℝ _ _)

/-- Failure of the hypotheses of (3): tile 6 has an edge (edge 2 = (6,2)-(4,0)) on the same line but lies on the other side
(vertex (6,0) has `u - v = 6 > 4`), so `hle` fails, and then the conclusion fails too: tile 2 edge 1 ∩ tile 6 edge 2
contains the two distinct points (4,0) and (5,1). -/
theorem c1_sameside_negative :
    ¬ (∀ y ∈ (D.tile (tl 6)).carrier, fL y ≤ 4 * Real.sqrt 3) ∧
    ¬ ((D.tile (tl 2)).edge 1 ∩ (D.tile (tl 6)).edge 2).Subsingleton := by
  constructor
  · intro h
    have hv : (D.tile (tl 6)).pts 1 ∈ (D.tile (tl 6)).carrier := subset_convexHull ℝ _ ⟨1, rfl⟩
    have := h _ hv
    rw [pt_toPt (tl 6) 1 (6, 0) (by decide +kernel), fL_toPt] at this
    push_cast at this
    nlinarith [s3pos]
  · intro h
    have a2 : (D.tile (tl 2)).pts 1 = toPt (4, 0) := pt_toPt _ _ _ (by decide +kernel)
    have b2 : (D.tile (tl 2)).pts (1 + 1) = toPt (5, 1) := pt_toPt _ _ _ (by decide +kernel)
    have a6 : (D.tile (tl 6)).pts 2 = toPt (6, 2) := pt_toPt _ _ _ (by decide +kernel)
    have b6 : (D.tile (tl 6)).pts (2 + 1) = toPt (4, 0) := pt_toPt _ _ _ (by decide +kernel)
    have m1 : toPt (4, 0) ∈ (D.tile (tl 2)).edge 1 ∩ (D.tile (tl 6)).edge 2 :=
      ⟨mem_edge_of _ 1 a2 b2 (left_mem_segment ℝ _ _), mem_edge_of _ 2 a6 b6 (right_mem_segment ℝ _ _)⟩
    have m2 : toPt (5, 1) ∈ (D.tile (tl 2)).edge 1 ∩ (D.tile (tl 6)).edge 2 :=
      ⟨mem_edge_of _ 1 a2 b2 (right_mem_segment ℝ _ _),
       mem_edge_of _ 2 a6 b6 (mem_seg_toPt (6, 2) (4, 0) (5, 1) (1/2) (by norm_num) (by norm_num)
         (by norm_num) (by norm_num))⟩
    have := (mkPt_inj (h m1 m2)).1
    unfold rx at this
    norm_num at this

end Erdos634.Draft.TJCC1App

#print axioms Erdos634.Draft.TJCC1App.c1_antiparallel
#print axioms Erdos634.Draft.TJCC1App.c1_sameside
#print axioms Erdos634.Draft.TJCC1App.c1_sameside_negative
