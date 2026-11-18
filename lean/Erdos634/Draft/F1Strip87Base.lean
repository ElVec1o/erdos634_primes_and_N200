/-
Draft/F1Strip87Base.lean -- the T_3 certificate of the tile (8,7,13) as input to the F1 strip lemma (Erdos #634).

`F1Strip87TilingBridge.dissection` is the kernel-checked dissection of the triangle with sides
`3 a b`, `3 b c`, `3 b (a+b)` (scale 26) into 945 copies of the tile.  The tiles were sorted so that the first
525 lie in the half-plane `p <= b` (`(X-Y)/(26 a) <= b`, for a vertex `(X, Y sqrt3)` in the scaled frame) and the last
420 in `p >= b`; this module checks that sorting by `decide +kernel` on the certificate, transfers it to the real
tiles, identifies the target with the triangle `T_3` of the strip lemma and the model with the half-cell, and feeds
`F1StripCert.f1_main`.  Conclusion: `T_m` is dissected into `m^2 * 7 * (8+7)` = `105 m^2` tiles for every `m >= 2`.

CREDIT: Yan Zhang (arXiv 2512.22696) for the family; Laczkovich for strip decompositions; the base tiling was found
by the project's exact search engine (bonfioli_tiling_engine).  UNAUDITED beyond the internal build.
No sorry, no native_decide.
-/
import Erdos634.Draft.F1Strip87TilingBridge
import Erdos634.Draft.F1StripCert

namespace Erdos634.Draft.F1Strip87Base

open Erdos634.Z3Real Erdos634.Geometry Erdos634.CertCoord Erdos634.Draft.F1StripGeom
  Erdos634.Draft.F1StripLemma Erdos634.Draft.F1StripDissect Erdos634.Draft.F1StripCert
open Erdos634.F1Strip87TilingBridge

noncomputable section

/-- a vertex has the shape `(x,0,0,y)` and `x - y` is below / above the line `s = 1` -/
def vertOK (lo : Bool) (v : F1Strip87Tiling.Pt) : Bool :=
  v.2.1 == 0 && v.2.2.1 == 0 &&
    (if lo then decide (v.1 - v.2.2.2 ≤ 1456) else decide (1456 ≤ v.1 - v.2.2.2))

def sideOK (lo : Bool) (t : F1Strip87Tiling.Tri) : Bool :=
  vertOK lo (F1Strip87Tiling.t1 t) && vertOK lo (F1Strip87Tiling.t2 t) && vertOK lo (F1Strip87Tiling.t3 t)

set_option maxRecDepth 400000 in
theorem tiles_length : F1Strip87Tiling.tiles.length = 945 := by decide +kernel

set_option maxRecDepth 400000 in
theorem left_ok : (F1Strip87Tiling.tiles.take 525).all (sideOK true) = true := by decide +kernel

set_option maxRecDepth 400000 in
theorem right_ok : (F1Strip87Tiling.tiles.drop 525).all (sideOK false) = true := by decide +kernel

theorem vertex_shape {lo : Bool} {t : F1Strip87Tiling.Tri} (h : sideOK lo t = true) (k : Fin 3) :
    vertOK lo (vertexOf t k) = true := by
  simp only [sideOK, Bool.and_eq_true] at h
  fin_cases k
  · exact h.1.1
  · exact h.1.2
  · exact h.2

theorem vertex_facts {lo : Bool} {v : F1Strip87Tiling.Pt} (h : vertOK lo v = true) :
    v.2.1 = 0 ∧ v.2.2.1 = 0 ∧
      (if lo then v.1 - v.2.2.2 ≤ 1456 else 1456 ≤ v.1 - v.2.2.2) := by
  simp only [vertOK, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨h1, h2, ?_⟩
  cases lo
  · simpa using h3
  · simpa using h3

theorem uA_pos : (0 : ℝ) < (26 : ℝ) * ((8 : ℕ) : ℝ) := by positivity

-- the tiles of the first block have p ≤ b on their whole carrier
set_option maxRecDepth 400000 in
theorem tile_left (i : Fin F1Strip87Tiling.tiles.length) (hi : i.val < 525) :
    ∀ x ∈ (pieceAt i).carrier, pc ((26 : ℝ) * ((8 : ℕ) : ℝ)) x ≤ ((7 : ℕ) : ℝ) := by
  have hmem : F1Strip87Tiling.tiles[i.val]'i.isLt ∈ F1Strip87Tiling.tiles.take 525 := by
    have h1 : i.val < (F1Strip87Tiling.tiles.take 525).length := by
      simp only [List.length_take]; omega
    have h2 : (F1Strip87Tiling.tiles.take 525)[i.val] = F1Strip87Tiling.tiles[i.val]'i.isLt := List.getElem_take ..
    rw [← h2]; exact List.getElem_mem h1
  have hs := List.all_eq_true.mp left_ok _ hmem
  refine pc_le_tile _ ((26 : ℝ) * ((7 : ℕ) : ℝ)) _ ?_
  intro k
  show pc _ ((pieceTri (t := F1Strip87Tiling.tiles[i.val]'i.isLt) (List.getElem_mem i.isLt)).pts k) ≤ _
  rw [pieceTri_pts _ _ k]
  obtain ⟨h1, h2, h3⟩ := vertex_facts (vertex_shape hs k)
  simp only [if_true] at h3
  exact pc_zpt_le h1 h2 uA_pos h3 (by norm_num)

-- the tiles of the second block have p ≥ b on their whole carrier
set_option maxRecDepth 400000 in
theorem tile_right (i : Fin F1Strip87Tiling.tiles.length) (hi : 525 ≤ i.val) :
    ∀ x ∈ (pieceAt i).carrier, ((7 : ℕ) : ℝ) ≤ pc ((26 : ℝ) * ((8 : ℕ) : ℝ)) x := by
  have hmem : F1Strip87Tiling.tiles[i.val]'i.isLt ∈ F1Strip87Tiling.tiles.drop 525 := by
    have h1 : i.val - 525 < (F1Strip87Tiling.tiles.drop 525).length := by
      simp only [List.length_drop]; have := i.isLt; omega
    have h2 : (F1Strip87Tiling.tiles.drop 525)[i.val - 525] = F1Strip87Tiling.tiles[i.val]'i.isLt := by
      rw [List.getElem_drop]; congr 1; omega
    rw [← h2]; exact List.getElem_mem h1
  have hs := List.all_eq_true.mp right_ok _ hmem
  refine pc_ge_tile _ ((26 : ℝ) * ((7 : ℕ) : ℝ)) _ ?_
  intro k
  show _ ≤ pc _ ((pieceTri (t := F1Strip87Tiling.tiles[i.val]'i.isLt) (List.getElem_mem i.isLt)).pts k)
  rw [pieceTri_pts _ _ k]
  obtain ⟨h1, h2, h3⟩ := vertex_facts (vertex_shape hs k)
  simp only [Bool.false_eq_true, if_false] at h3
  exact pc_zpt_ge h1 h2 uA_pos h3 (by norm_num)

/-- the target of the certificate is the triangle `T_3` of the strip lemma -/
theorem target_carrier :
    dissection.target.carrier =
      triR ((26 : ℝ) * ((8 : ℕ) : ℝ)) ((26 : ℝ) * ((7 : ℕ) : ℝ)) ((8 : ℕ) : ℝ) ((7 : ℕ) : ℝ) 3 := by
  have hA : (0 : ℝ) < ((8 : ℕ) : ℝ) := by positivity
  have hB : (0 : ℝ) < ((7 : ℕ) : ℝ) := by positivity
  have ha : (0 : ℝ) < (26 : ℝ) * ((8 : ℕ) : ℝ) := by positivity
  have hb : (0 : ℝ) < (26 : ℝ) * ((7 : ℕ) : ℝ) := by positivity
  rw [← carrier_targ ha hb hA hB 3 (by norm_num)]
  have heq : dissection.target = targTri ha hb hA hB 3 (by norm_num) := by
    show targetTri = _
    apply tri_ext
    funext k
    rw [targetTri_pts_eq k]
    fin_cases k
    · simp [targTri, F1Strip87Tiling.target, F1Strip87Tiling.t1, zx, zy, toR, toZPt]
    · simp [targTri, F1Strip87Tiling.target, F1Strip87Tiling.t2, zx, zy, toR, toZPt]
      norm_num
    · simp [targTri, F1Strip87Tiling.target, F1Strip87Tiling.t3, zx, zy, toR, r3, toZPt]
      congr 1 <;> ring
  rw [heq]

theorem model_cong :
    dissection.model.Congruent (model (by norm_num : 0 < 8) (by norm_num : 0 < 7) (by norm_num : (0 : ℝ) < 26)) := by
  obtain ⟨m1, m2, m3⟩ := model_sides
  refine model_congruent_of_sq (C := 13) _ _ _ (by norm_num) ?_ ?_ ?_
  · show dist ((pieceTri headI_mem_tiles).pts 0) ((pieceTri headI_mem_tiles).pts 1) ^ 2 = _
    rw [m1]; norm_num
  · show dist ((pieceTri headI_mem_tiles).pts 1) ((pieceTri headI_mem_tiles).pts 2) ^ 2 = _
    rw [m2]; norm_num
  · show dist ((pieceTri headI_mem_tiles).pts 2) ((pieceTri headI_mem_tiles).pts 0) ^ 2 = _
    rw [m3]; norm_num

/-- **The strip lemma applied to the certificate**: `T_m` is dissected into `m² * 7 * (8+7)` tiles
for every `m ≥ 2`, with target sides `m u a b`, `m u b c`, `m u b (a+b)` and tile sides `u a`, `u b`, `u c` (here `u = 26`). -/
theorem f1_87_dissections :
    ∀ m : ℕ, 2 ≤ m → ∃ E : CongruentDissection (m * m * (7 * (8 + 7))),
      dist (E.target.pts 0) (E.target.pts 1) = (m : ℝ) * (26 : ℝ) * ((8 : ℕ) : ℝ) * ((7 : ℕ) : ℝ) ∧
      dist (E.target.pts 1) (E.target.pts 2) = (m : ℝ) * (26 : ℝ) * ((7 : ℕ) : ℝ) * ((13 : ℕ) : ℝ) ∧
      dist (E.target.pts 2) (E.target.pts 0) = (m : ℝ) * (26 : ℝ) * ((7 : ℕ) : ℝ) * (((8 : ℕ) : ℝ) + ((7 : ℕ) : ℝ)) ∧
      dist (E.model.pts 0) (E.model.pts 1) = (26 : ℝ) * ((8 : ℕ) : ℝ) ∧
      dist (E.model.pts 1) (E.model.pts 2) = (26 : ℝ) * ((7 : ℕ) : ℝ) ∧
      dist (E.model.pts 2) (E.model.pts 0) = (26 : ℝ) * ((13 : ℕ) : ℝ) :=
  f1_main (A := 8) (B := 7) (C := 13) (by norm_num) (by norm_num) (u := 26) (by norm_num) (by norm_num)
    (N := F1Strip87Tiling.tiles.length) (n₁ := 525) (n₂ := 420)
    (by have := tiles_length; omega) (by norm_num) (by norm_num)
    dissection target_carrier model_cong
    (fun i hi x hx => tile_left i hi x hx) (fun i hi x hx => tile_right i hi x hx)

end

end Erdos634.Draft.F1Strip87Base

#print axioms Erdos634.Draft.F1Strip87Base.f1_87_dissections
