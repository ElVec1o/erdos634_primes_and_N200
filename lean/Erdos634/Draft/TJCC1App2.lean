-- No sorry, no native_decide.
-- C1 continued: `wall_cover` (both sides of the T-junction wall (4,0)-(6,2)), `edge_interior_or_side`, `eDir_of_side`,
-- and the failure of the conclusion at the T-vertex (5,1).
import Erdos634.Draft.TJCC1App

namespace Erdos634.Draft.TJCC1App2

open Erdos634.Geometry Erdos634.CertCoord Erdos634.Draft.TJCHelp Erdos634.Draft.G3CCert
  Erdos634.Draft.G3RCCommon Erdos634.Draft.G3RC1Tiling Erdos634.Draft.TJCC1 Erdos634.Draft.TJCC1App

theorem tgt_pts (k : Fin 3) : D.target.pts k = toPt (vtx cert.target k) := by
  show (cd cert cert_ok).target.pts k = _
  rw [cd_target, triOf_pts]

theorem tgt_coord (a β : ℝ) (k : Fin 3) :
    D.target.basis.coord k (mkPt a (β * Real.sqrt 3)) = ![(8 - a - β) / 8, (a - β) / 8, β / 4] k := by
  refine Erdos634.Subdivision.Tri.coord_eq_of_combo D.target _ _ ?_ ?_ k
  · simp; ring
  · rw [tgt_pts 0, tgt_pts 1, tgt_pts 2]
    have v0 : vtx cert.target 0 = (0, 0) := rfl
    have v1 : vtx cert.target 1 = (8, 0) := rfl
    have v2 : vtx cert.target 2 = (4, 4) := rfl
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    rw [v0, v1, v2, toPt_eq, toPt_eq, toPt_eq, mkPt_smul, mkPt_smul, mkPt_smul, TJCHelp.mkPt_add, TJCHelp.mkPt_add]
    congr 1 <;> push_cast <;> ring

theorem tgt_interior (a β : ℝ) (h1 : 0 < β) (h2 : β < a) (h3 : a + β < 8) :
    mkPt a (β * Real.sqrt 3) ∈ interior D.target.carrier := by
  apply interior_of_pos
  intro k
  rw [tgt_coord]
  fin_cases k <;> simp <;> linarith

theorem wall_pts (y : Plane) (hy : y ∈ openSegment ℝ (toPt (4, 0)) (toPt (6, 2))) :
    ∃ b : ℝ, 0 < b ∧ b < 1 ∧ y = mkPt (4 + 2 * b) ((2 * b) * Real.sqrt 3) := by
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hy
  refine ⟨b, hb, by linarith, ?_⟩
  have ha' : a = 1 - b := by linarith
  rw [toPt_eq, toPt_eq, mkPt_smul, mkPt_smul, TJCHelp.mkPt_add]
  congr 1 <;> push_cast <;> rw [ha'] <;> ring

theorem c1_hint : openSegment ℝ (toPt (4, 0)) (toPt (6, 2)) ⊆ interior D.target.carrier := by
  intro y hy
  obtain ⟨b, hb0, hb1, rfl⟩ := wall_pts y hy
  exact tgt_interior (4 + 2 * b) (2 * b) (by linarith) (by linarith) (by linarith)

theorem c1_hS : segment ℝ (toPt (4, 0)) (toPt (6, 2)) ⊆ {y | fL y = 4 * Real.sqrt 3} :=
  fun y hy => seg_eq (by rw [fL_toPt]; push_cast; ring) (by rw [fL_toPt]; push_cast; ring) hy

theorem side_all : ∀ i : Fin cert.leaves.length,
    (∀ k, (vtx (cert.leaves.get i) k).1 - (vtx (cert.leaves.get i) k).2 ≤ 4) ∨
    (∀ k, 4 ≤ (vtx (cert.leaves.get i) k).1 - (vtx (cert.leaves.get i) k).2) := by decide +kernel

/-- every tile of C1 lies on one side of the T-junction line `u - v = 4`, so no tile has an interior point on the wall -/
theorem c1_hwall : ∀ y ∈ openSegment ℝ (toPt (4, 0)) (toPt (6, 2)), ∀ i, y ∉ interior (D.tile i).carrier := by
  intro y hy i hyi
  have hfy : fL y = 4 * Real.sqrt 3 := c1_hS (openSegment_subset_segment ℝ _ _ hy)
  rcases side_all i with h | h
  · exact not_interior_on_line fL_ne (c := 4 * Real.sqrt 3) (A := (D.tile i).carrier)
      (carrier_le (D.tile i) (side_le i h)) hyi hfy
  · exact not_interior_on_line_ge fL_ne (c := 4 * Real.sqrt 3) (A := (D.tile i).carrier)
      (carrier_ge (D.tile i) (side_ge i h)) hyi hfy

theorem c1_hu : toPt (4, 0) ≠ toPt (6, 2) := fun h => by
  have := (mkPt_inj h).1; unfold rx at this; norm_num at this

theorem X_in_wall : X ∈ openSegment ℝ (toPt (4, 0)) (toPt (6, 2)) :=
  X_oseg (4, 0) (6, 2) (1/4) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem fL_eq_int (i : Fin cert.leaves.length) (k : Fin 3) (h : fL ((D.tile i).pts k) = 4 * Real.sqrt 3) :
    (vtx (cert.leaves.get i) k).1 - (vtx (cert.leaves.get i) k).2 = 4 := by
  rw [tile_pts_gen, fL_toPt] at h
  have h' : Real.sqrt 3 * (((vtx (cert.leaves.get i) k).1 : ℝ) - (vtx (cert.leaves.get i) k).2)
      = Real.sqrt 3 * 4 := by rw [h]; ring
  have := mul_left_cancel₀ s3pos.ne' h'
  exact_mod_cast this

theorem fL_le_int (i : Fin cert.leaves.length) (k : Fin 3) (h : fL ((D.tile i).pts k) ≤ 4 * Real.sqrt 3) :
    (vtx (cert.leaves.get i) k).1 - (vtx (cert.leaves.get i) k).2 ≤ 4 := by
  rw [tile_pts_gen, fL_toPt] at h
  have h' : Real.sqrt 3 * (((vtx (cert.leaves.get i) k).1 : ℝ) - (vtx (cert.leaves.get i) k).2)
      ≤ Real.sqrt 3 * 4 := by linarith
  have := le_of_mul_le_mul_left h' s3pos
  exact_mod_cast this

theorem chain_near : ∀ i : Fin cert.leaves.length, ∀ k : Fin 3,
    (vtx (cert.leaves.get i) k).1 - (vtx (cert.leaves.get i) k).2 = 4 →
    (vtx (cert.leaves.get i) (k + 1)).1 - (vtx (cert.leaves.get i) (k + 1)).2 = 4 →
    (∀ k', (vtx (cert.leaves.get i) k').1 - (vtx (cert.leaves.get i) k').2 ≤ 4) →
    (i.val = 2 ∨ i.val = 3) ∧ k = 1 := by decide +kernel

/-! ## (2) `wall_cover`, near side (`f ≤ c`: tiles 0-5): the chain edge through X is tile 2's edge 1 -/

theorem c1_wall_cover_near :
    ∃ e ∈ D.lineChain fL (4 * Real.sqrt 3), X ∈ (D.tile e.1).edge e.2 ∧ e = (tl 2, 1) := by
  obtain ⟨e, he, hxe⟩ := D.wall_cover fL (4 * Real.sqrt 3) fL_ne c1_hu c1_hS c1_hint c1_hwall X_in_wall X_not_vertex
  refine ⟨e, he, hxe, ?_⟩
  obtain ⟨i, k⟩ := e
  rw [Dissection.mem_lineChain] at he
  obtain ⟨h1, h2, h3⟩ := he
  simp only at h1 h2 h3 hxe
  obtain ⟨hi, hk⟩ := chain_near i k (fL_eq_int _ _ h1) (fL_eq_int _ _ h2) (fun k' => fL_le_int _ _ (h3 k'))
  rcases hi with hi | hi
  · exact Prod.ext (Fin.ext hi) hk
  · exfalso
    have hi' : i = tl 3 := Fin.ext hi
    subst hi'; subst hk
    -- X lies on tile 3's edge 1 = segment (5,1)-(6,2), where the first coordinate is ≥ 5
    have a3 : (D.tile (tl 3)).pts 1 = toPt (5, 1) := pt_toPt _ _ _ (by decide +kernel)
    have b3 : (D.tile (tl 3)).pts (1 + 1) = toPt (6, 2) := pt_toPt _ _ _ (by decide +kernel)
    unfold Tri.edge at hxe; rw [a3, b3] at hxe
    have := seg_le (f := lin (-1) 0) (c := -5) (p := toPt (5, 1)) (q := toPt (6, 2)) (y := X)
      (by rw [lin_toPt]; norm_num) (by rw [lin_toPt]; norm_num) hxe
    have e : lin (-1) 0 X = -(9 / 2) := by unfold X; rw [lin_mkPt]; ring
    rw [e] at this; norm_num at this

/-! ## (2') `wall_cover`, far side (the T-junction long edge of tile 6): `g = -f`, `c = -4√3` -/

noncomputable abbrev gL : Plane →ₗ[ℝ] ℝ := lin (-Real.sqrt 3) 1

theorem gL_toPt (p : LP) : gL (toPt p) = -(Real.sqrt 3 * ((p.1 : ℝ) - p.2)) := by
  rw [lin_toPt]; ring

theorem gL_ne : gL ≠ 0 := lin_ne_zero (Or.inr one_ne_zero)

theorem c1_hS_g : segment ℝ (toPt (4, 0)) (toPt (6, 2)) ⊆ {y | gL y = -(4 * Real.sqrt 3)} :=
  fun y hy => seg_eq (by rw [gL_toPt]; push_cast; ring) (by rw [gL_toPt]; push_cast; ring) hy

theorem gL_eq_int (i : Fin cert.leaves.length) (k : Fin 3) (h : gL ((D.tile i).pts k) = -(4 * Real.sqrt 3)) :
    (vtx (cert.leaves.get i) k).1 - (vtx (cert.leaves.get i) k).2 = 4 := by
  rw [tile_pts_gen, gL_toPt] at h
  have h' : Real.sqrt 3 * (((vtx (cert.leaves.get i) k).1 : ℝ) - (vtx (cert.leaves.get i) k).2)
      = Real.sqrt 3 * 4 := by linarith
  have := mul_left_cancel₀ s3pos.ne' h'
  exact_mod_cast this

theorem gL_le_int (i : Fin cert.leaves.length) (k : Fin 3) (h : gL ((D.tile i).pts k) ≤ -(4 * Real.sqrt 3)) :
    4 ≤ (vtx (cert.leaves.get i) k).1 - (vtx (cert.leaves.get i) k).2 := by
  rw [tile_pts_gen, gL_toPt] at h
  have h' : Real.sqrt 3 * 4 ≤ Real.sqrt 3 * (((vtx (cert.leaves.get i) k).1 : ℝ) - (vtx (cert.leaves.get i) k).2) := by
    linarith
  have := le_of_mul_le_mul_left h' s3pos
  exact_mod_cast this

theorem chain_far : ∀ i : Fin cert.leaves.length, ∀ k : Fin 3,
    (vtx (cert.leaves.get i) k).1 - (vtx (cert.leaves.get i) k).2 = 4 →
    (vtx (cert.leaves.get i) (k + 1)).1 - (vtx (cert.leaves.get i) (k + 1)).2 = 4 →
    (∀ k', 4 ≤ (vtx (cert.leaves.get i) k').1 - (vtx (cert.leaves.get i) k').2) →
    i.val = 6 ∧ k = 2 := by decide +kernel

theorem c1_wall_cover_far :
    ∃ e ∈ D.lineChain gL (-(4 * Real.sqrt 3)), X ∈ (D.tile e.1).edge e.2 ∧ e = (tl 6, 2) := by
  obtain ⟨e, he, hxe⟩ := D.wall_cover gL (-(4 * Real.sqrt 3)) gL_ne c1_hu c1_hS_g c1_hint c1_hwall X_in_wall X_not_vertex
  refine ⟨e, he, hxe, ?_⟩
  obtain ⟨i, k⟩ := e
  rw [Dissection.mem_lineChain] at he
  obtain ⟨h1, h2, h3⟩ := he
  simp only at h1 h2 h3 hxe
  obtain ⟨hi, hk⟩ := chain_far i k (gL_eq_int _ _ h1) (gL_eq_int _ _ h2) (fun k' => gL_le_int _ _ (h3 k'))
  exact Prod.ext (Fin.ext hi) hk

end Erdos634.Draft.TJCC1App2

#print axioms Erdos634.Draft.TJCC1App2.c1_wall_cover_near
#print axioms Erdos634.Draft.TJCC1App2.c1_wall_cover_far
#print axioms Erdos634.Draft.TJCC1App2.c1_hwall
#print axioms Erdos634.Draft.TJCC1App2.c1_hint
