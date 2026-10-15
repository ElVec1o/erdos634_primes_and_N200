/-
Coordinate toolkit for the corner parallelogram on the N = 44 tiling.  The witness follows `Draft/GLCWit3.lean`
(gamma = 2alpha, the N = 1125 tiling) and `Draft/GammaTrapWitness44.lean` / `Draft/ApexWitness44.lean` (the N = 44 base-beta
tiling `D44`, whose coordinates, model relabelling `τ` and scalar facts are imported and used here: `D44`, `model_s0/1/2`,
`D44_hα/hβ/hγ`, `D44_angleData`, `tgt_hb0/1`, `D44_hcorner`, `pieceTri_pts`, `pieceTri_dist_sq`).  Imports `CornerParaMaster`.
-/
import Erdos634.Draft.CornerParaMaster
import Erdos634.Draft.GammaTrapWitness44

/-!
# CP-5 (Witness), part 3a of 3: the real N = 44 tiling `D44`: model, shape, coordinates, identification of the corner tiles  The real kernel-checked base-β tiling
`D44 = Tiling44Bridge.dissection.relabelModel τ` (`N = 44`, `(e, f, s) = (1, 2, 8)`: tile sides `16 = a`, `24 = b`, `32 = c`; target
`(0, 0)`, `(176, 0)`, `(88, 24√15)` with base angles `β` at vertices `0`, `1` and apex `3α` at vertex `2`) satisfies EVERY hypothesis
of `corner_parallelogram` (`D44_model`, `D44_shape`, `D44_angleData`, the corner hypotheses `tgt_hb0`, `tgt_hb1`) — so the master
statement is about a real instance, not a vacuous one.  This file holds the toolkit for pinning its conclusion in Lean:

* `D44_model`, `D44_shape`, `D44_iso₁`, `D44_iso₂` (the isosceles reading with apex `2`);
* the coordinate toolkit (`D44_pts`, `D44_dist`, `D44_same`, `D44_same_tgt`: vertices and squared distances of the real tiles read
  through `pieceTri_pts` / `pieceTri_dist_sq` from the `ℤ[√15]` data of `Tiling44.tiles`, the `decide`-checked vertex descriptors);
* `D44_beta`, `D44_ident`: a tile whose vertex `j` has opposite side `24 = b` presents `β` there, hence is THE forward tile;
* `D44_corner0_chord`, `D44_corner1_chord`: at the base corners `0` and `1` the corner tile is `tiles[0]` resp. `tiles[13]`, its chord
  ends are given by their vertices, the partner `T_3` is `tiles[2]` (edge `2`) resp. `tiles[14]` (edge `0`) and its third vertex is `P + Q − A`;
* the four forward-edge pins `D44_pin_P0 / Q0 / P1 / Q1` (which vertex of the forward tile is the far end of the forward edge,
  and the edge length), by the `y`-coordinate of the real vertices.
-/

namespace Erdos634.CornerPara.Witness44

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.Z15Real Erdos634.Tiling44Bridge
  Erdos634.BaseBetaTargetCoord Erdos634.Draft.ApexWitness44 Erdos634.Draft.GammaTrapWitness44
  Erdos634.CornerPara

/-! ## 1. The hypotheses of the master theorem at the real tiling -/

/-- **`BaseBetaModel` at the real 44-tiling**: `(e, f, s) = (1, 2, 8)`, sides `16, 24, 32`. -/
theorem D44_model :
    BaseBetaModel D44 1 2 8 (modelAlpha 1 ((2 : ℕ) : ℝ)) (modelBeta 1 ((2 : ℕ) : ℝ))
      (2 * modelAlpha 1 ((2 : ℕ) : ℝ) + modelBeta 1 ((2 : ℕ) : ℝ)) where
  hs := by norm_num
  hs0 := by rw [model_s0]; norm_num
  hs1 := by rw [model_s1]; norm_num
  hs2 := by rw [model_s2]; norm_num
  hα' := D44_hα
  hβ' := D44_hβ
  hγ' := D44_hγ

/-- **`BaseBetaShape` at the real 44-tiling**: corners `(β, β, 3α)`. -/
theorem D44_shape :
    BaseBetaShape D44.target (modelAlpha 1 ((2 : ℕ) : ℝ)) (modelBeta 1 ((2 : ℕ) : ℝ)) := by
  intro m
  fin_cases m
  · right; exact tgt_hb0
  · right; exact tgt_hb1
  · left; exact D44_hcorner

/-- The isosceles reading of the 44-target with apex `2`: the corner at `a + 1 = 0` is `β` ... -/
theorem D44_iso₁ :
    cornerAngle (D44.target.pts (2 + 1 + 1)) (D44.target.pts (2 + 1)) (D44.target.pts (2 + 1 + 2)) =
      modelBeta 1 ((2 : ℕ) : ℝ) := tgt_hb0

/-- ... and the corner at `a + 2 = 1` is `β`. -/
theorem D44_iso₂ :
    cornerAngle (D44.target.pts (2 + 2 + 1)) (D44.target.pts (2 + 2)) (D44.target.pts (2 + 2 + 2)) =
      modelBeta 1 ((2 : ℕ) : ℝ) := tgt_hb1

/-! ## 2. Coordinate toolkit: vertices and distances of the real tiles -/

theorem D44_pts (a : Fin Tiling44.tiles.length) (j : Fin 3) :
    (D44.tile a).pts j = Erdos634.CertCoord.mkPt (toR (zx (toZPt (vertexOf Tiling44.tiles[a.val] j))))
      (toR (zy (toZPt (vertexOf Tiling44.tiles[a.val] j)))) := by
  show (pieceAt a).pts j = _
  unfold pieceAt
  exact pieceTri_pts _ _ _

theorem D44_tgt_pts (k : Fin 3) : D44.target.pts k = Erdos634.CertCoord.mkPt
    (toR (zx (toZPt (![Tiling44.t1 Tiling44.target, Tiling44.t2 Tiling44.target, Tiling44.t3 Tiling44.target] k))))
    (toR (zy (toZPt (![Tiling44.t1 Tiling44.target, Tiling44.t2 Tiling44.target, Tiling44.t3 Tiling44.target] k)))) :=
  targetTri_pts_eq k

theorem D44_dist_sq (a : Fin Tiling44.tiles.length) (i j : Fin 3) :
    dist ((D44.tile a).pts i) ((D44.tile a).pts j) ^ 2 =
      toR (Tiling44.dist2 (vertexOf Tiling44.tiles[a.val] i) (vertexOf Tiling44.tiles[a.val] j)) := by
  show dist ((pieceAt a).pts i) ((pieceAt a).pts j) ^ 2 = _
  unfold pieceAt
  exact pieceTri_dist_sq _ _ i j

theorem D44_dist (a : Fin Tiling44.tiles.length) (i j : Fin 3) (v : ℤ) (s : ℝ) (hs : 0 ≤ s)
    (hv : Tiling44.dist2 (vertexOf Tiling44.tiles[a.val] i) (vertexOf Tiling44.tiles[a.val] j) = (v, 0))
    (hvs : (v : ℝ) = s ^ 2) : dist ((D44.tile a).pts i) ((D44.tile a).pts j) = s := by
  apply dist_of_sq hs _ (by rw [← hvs])
  rw [D44_dist_sq, hv]; simp [toR]

theorem D44_same (a b : Fin Tiling44.tiles.length) (i j : Fin 3)
    (h : vertexOf Tiling44.tiles[a.val] i = vertexOf Tiling44.tiles[b.val] j) :
    (D44.tile a).pts i = (D44.tile b).pts j := by
  rw [D44_pts, D44_pts, h]

theorem D44_same_tgt (k : Fin 3) (a : Fin Tiling44.tiles.length) (i : Fin 3)
    (h : ![Tiling44.t1 Tiling44.target, Tiling44.t2 Tiling44.target, Tiling44.t3 Tiling44.target] k =
      vertexOf Tiling44.tiles[a.val] i) : D44.target.pts k = (D44.tile a).pts i := by
  rw [D44_tgt_pts, D44_pts, h]

/-- The tiles of `D44` that occur at the base corners (indices into `Tiling44.tiles`). -/
def i0 : Fin Tiling44.tiles.length := ⟨0, by decide⟩
def i1 : Fin Tiling44.tiles.length := ⟨1, by decide⟩
def i2 : Fin Tiling44.tiles.length := ⟨2, by decide⟩
def i11 : Fin Tiling44.tiles.length := ⟨11, by decide⟩
def i13 : Fin Tiling44.tiles.length := ⟨13, by decide⟩
def i14 : Fin Tiling44.tiles.length := ⟨14, by decide⟩
def i22 : Fin Tiling44.tiles.length := ⟨22, by decide⟩
def i28 : Fin Tiling44.tiles.length := ⟨28, by decide⟩

/-- A tile whose vertex `j` has opposite side `24 = b` presents `β` there. -/
theorem D44_beta (a : Fin Tiling44.tiles.length) (j : Fin 3)
    (h : dist ((D44.tile a).pts (j + 1)) ((D44.tile a).pts (j + 2)) = 24) :
    (D44.tile a).localAngle ((D44.tile a).pts j) = modelBeta 1 ((2 : ℕ) : ℝ) :=
  (D44_model.localAngle_of_oppSide (by decide) le_rfl (by norm_num) a j).2.1 (by rw [h, model_s1])

/-- Uniqueness of the forward tile: if `K` is the forward tile at `X` and a candidate tile `c` has `X` as its vertex `j` with
opposite side `24 = b`, then `K = c`. -/
theorem D44_ident {X V : Plane} {K : Fin Tiling44.tiles.length}
    (hK : ForwardTile D44 (modelBeta 1 ((2 : ℕ) : ℝ)) X V K) (c : Fin Tiling44.tiles.length) (j : Fin 3)
    (hX : (D44.tile c).pts j = X) (h : dist ((D44.tile c).pts (j + 1)) ((D44.tile c).pts (j + 2)) = 24) : K = c :=
  (hK.uniq c (by rw [← hX]; exact D44_beta c j h)).symm

/-! ## 3. Vertex descriptors of the real tiles (checked by `decide` in `ℤ[√15]`) -/

theorem vt0_0 : vertexOf Tiling44.tiles[0] 0 = (0, 0, 0, 0) := by decide
theorem vt0_1 : vertexOf Tiling44.tiles[0] 1 = (16, 0, 0, 0) := by decide
theorem vt0_2 : vertexOf Tiling44.tiles[0] 2 = (22, 0, 0, 6) := by decide
theorem vt1_0 : vertexOf Tiling44.tiles[1] 0 = (16, 0, 0, 0) := by decide
theorem vt1_1 : vertexOf Tiling44.tiles[1] 1 = (32, 0, 0, 0) := by decide
theorem vt1_2 : vertexOf Tiling44.tiles[1] 2 = (38, 0, 0, 6) := by decide
theorem vt2_0 : vertexOf Tiling44.tiles[2] 0 = (16, 0, 0, 0) := by decide
theorem vt2_1 : vertexOf Tiling44.tiles[2] 1 = (38, 0, 0, 6) := by decide
theorem vt2_2 : vertexOf Tiling44.tiles[2] 2 = (22, 0, 0, 6) := by decide
theorem vt11_0 : vertexOf Tiling44.tiles[11] 0 = (128, 0, 0, 0) := by decide
theorem vt11_1 : vertexOf Tiling44.tiles[11] 1 = (160, 0, 0, 0) := by decide
theorem vt11_2 : vertexOf Tiling44.tiles[11] 2 = (149, 0, 0, 3) := by decide
theorem vt13_0 : vertexOf Tiling44.tiles[13] 0 = (160, 0, 0, 0) := by decide
theorem vt13_1 : vertexOf Tiling44.tiles[13] 1 = (176, 0, 0, 0) := by decide
theorem vt13_2 : vertexOf Tiling44.tiles[13] 2 = (154, 0, 0, 6) := by decide
theorem vt14_0 : vertexOf Tiling44.tiles[14] 0 = (160, 0, 0, 0) := by decide
theorem vt14_1 : vertexOf Tiling44.tiles[14] 1 = (154, 0, 0, 6) := by decide
theorem vt14_2 : vertexOf Tiling44.tiles[14] 2 = (138, 0, 0, 6) := by decide
theorem vt22_0 : vertexOf Tiling44.tiles[22] 0 = (22, 0, 0, 6) := by decide
theorem vt22_1 : vertexOf Tiling44.tiles[22] 1 = (38, 0, 0, 6) := by decide
theorem vt22_2 : vertexOf Tiling44.tiles[22] 2 = (44, 0, 0, 12) := by decide
theorem vt28_0 : vertexOf Tiling44.tiles[28] 0 = (122, 0, 0, 6) := by decide
theorem vt28_1 : vertexOf Tiling44.tiles[28] 1 = (154, 0, 0, 6) := by decide
theorem vt28_2 : vertexOf Tiling44.tiles[28] 2 = (143, 0, 0, 9) := by decide
theorem vtT_0 : (![Tiling44.t1 Tiling44.target, Tiling44.t2 Tiling44.target, Tiling44.t3 Tiling44.target]
    (0 : Fin 3)) = (0, 0, 0, 0) := by decide
theorem vtT_1 : (![Tiling44.t1 Tiling44.target, Tiling44.t2 Tiling44.target, Tiling44.t3 Tiling44.target]
    (1 : Fin 3)) = (176, 0, 0, 0) := by decide
theorem vtT_2 : (![Tiling44.t1 Tiling44.target, Tiling44.t2 Tiling44.target, Tiling44.t3 Tiling44.target]
    (2 : Fin 3)) = (88, 0, 0, 24) := by decide

-- squared lengths (`decide`): the opposite sides `24² = 576` of the forward tiles, the flank lengths of the corner tiles,
-- and the forward edges (`16² = 256`, `32² = 1024`)
theorem d1_12 : Tiling44.dist2 (vertexOf Tiling44.tiles[1] 1) (vertexOf Tiling44.tiles[1] 2) = (576, 0) := by decide
theorem d22_12 : Tiling44.dist2 (vertexOf Tiling44.tiles[22] 1) (vertexOf Tiling44.tiles[22] 2) = (576, 0) := by decide
theorem d11_20 : Tiling44.dist2 (vertexOf Tiling44.tiles[11] 2) (vertexOf Tiling44.tiles[11] 0) = (576, 0) := by decide
theorem d28_20 : Tiling44.dist2 (vertexOf Tiling44.tiles[28] 2) (vertexOf Tiling44.tiles[28] 0) = (576, 0) := by decide
theorem d0_02 : Tiling44.dist2 (vertexOf Tiling44.tiles[0] 0) (vertexOf Tiling44.tiles[0] 2) = (1024, 0) := by decide
theorem d13_12 : Tiling44.dist2 (vertexOf Tiling44.tiles[13] 1) (vertexOf Tiling44.tiles[13] 2) = (1024, 0) := by decide
theorem d1_01 : Tiling44.dist2 (vertexOf Tiling44.tiles[1] 0) (vertexOf Tiling44.tiles[1] 1) = (256, 0) := by decide
theorem d22_02 : Tiling44.dist2 (vertexOf Tiling44.tiles[22] 0) (vertexOf Tiling44.tiles[22] 2) = (1024, 0) := by decide
theorem d11_10 : Tiling44.dist2 (vertexOf Tiling44.tiles[11] 1) (vertexOf Tiling44.tiles[11] 0) = (1024, 0) := by decide
theorem d28_12 : Tiling44.dist2 (vertexOf Tiling44.tiles[28] 1) (vertexOf Tiling44.tiles[28] 2) = (256, 0) := by decide

/-! ## 4. Coordinates (`mkPt x y`) of the vertices used by the pins -/

open Erdos634.CertCoord in
theorem coord_A0 : D44.target.pts 0 = mkPt 0 0 := by
  rw [D44_tgt_pts, vtT_0]; simp [toZPt, zx, zy, toR]
open Erdos634.CertCoord in
theorem coord_A1 : D44.target.pts 1 = mkPt 176 0 := by
  rw [D44_tgt_pts, vtT_1]; simp [toZPt, zx, zy, toR]
open Erdos634.CertCoord in
theorem coord_A2 : D44.target.pts 2 = mkPt 88 (24 * Real.sqrt 15) := by
  rw [D44_tgt_pts, vtT_2]; simp [toZPt, zx, zy, toR]
open Erdos634.CertCoord in
theorem coord_t0_1 : (D44.tile i0).pts 1 = mkPt 16 0 := by
  rw [D44_pts]; simp only [i0]; rw [vt0_1]; simp [toZPt, zx, zy, toR]
open Erdos634.CertCoord in
theorem coord_t0_2 : (D44.tile i0).pts 2 = mkPt 22 (6 * Real.sqrt 15) := by
  rw [D44_pts]; simp only [i0]; rw [vt0_2]; simp [toZPt, zx, zy, toR]
open Erdos634.CertCoord in
theorem coord_t1_2 : (D44.tile i1).pts 2 = mkPt 38 (6 * Real.sqrt 15) := by
  rw [D44_pts]; simp only [i1]; rw [vt1_2]; simp [toZPt, zx, zy, toR]
open Erdos634.CertCoord in
theorem coord_t22_1 : (D44.tile i22).pts 1 = mkPt 38 (6 * Real.sqrt 15) := by
  rw [D44_pts]; simp only [i22]; rw [vt22_1]; simp [toZPt, zx, zy, toR]
open Erdos634.CertCoord in
theorem coord_t13_0 : (D44.tile i13).pts 0 = mkPt 160 0 := by
  rw [D44_pts]; simp only [i13]; rw [vt13_0]; simp [toZPt, zx, zy, toR]
open Erdos634.CertCoord in
theorem coord_t13_2 : (D44.tile i13).pts 2 = mkPt 154 (6 * Real.sqrt 15) := by
  rw [D44_pts]; simp only [i13]; rw [vt13_2]; simp [toZPt, zx, zy, toR]
open Erdos634.CertCoord in
theorem coord_t11_2 : (D44.tile i11).pts 2 = mkPt 149 (3 * Real.sqrt 15) := by
  rw [D44_pts]; simp only [i11]; rw [vt11_2]; simp [toZPt, zx, zy, toR]
open Erdos634.CertCoord in
theorem coord_t28_0 : (D44.tile i28).pts 0 = mkPt 122 (6 * Real.sqrt 15) := by
  rw [D44_pts]; simp only [i28]; rw [vt28_0]; simp [toZPt, zx, zy, toR]

open Erdos634.CertCoord in
theorem coord_t1_0 : (D44.tile i1).pts 0 = mkPt 16 0 := by
  rw [D44_pts]; simp only [i1]; rw [vt1_0]; simp [toZPt, zx, zy, toR]
open Erdos634.CertCoord in
theorem coord_t2_1 : (D44.tile i2).pts 1 = mkPt 38 (6 * Real.sqrt 15) := by
  rw [D44_pts]; simp only [i2]; rw [vt2_1]; simp [toZPt, zx, zy, toR]
open Erdos634.CertCoord in
theorem coord_t22_0 : (D44.tile i22).pts 0 = mkPt 22 (6 * Real.sqrt 15) := by
  rw [D44_pts]; simp only [i22]; rw [vt22_0]; simp [toZPt, zx, zy, toR]
open Erdos634.CertCoord in
theorem coord_t11_1 : (D44.tile i11).pts 1 = mkPt 160 0 := by
  rw [D44_pts]; simp only [i11]; rw [vt11_1]; simp [toZPt, zx, zy, toR]
open Erdos634.CertCoord in
theorem coord_t14_2 : (D44.tile i14).pts 2 = mkPt 138 (6 * Real.sqrt 15) := by
  rw [D44_pts]; simp only [i14]; rw [vt14_2]; simp [toZPt, zx, zy, toR]
open Erdos634.CertCoord in
theorem coord_t28_1 : (D44.tile i28).pts 1 = mkPt 154 (6 * Real.sqrt 15) := by
  rw [D44_pts]; simp only [i28]; rw [vt28_1]; simp [toZPt, zx, zy, toR]

/-! ## 5. The corner chords of the real tiling, identified -/

/-- **Corner `k = 0`, `A = (0, 0)`, identified.**  The corner tile is `tiles[0]`; `P = tiles[0].pts 1 = (16, 0)` (the `γ` end),
`Q = tiles[0].pts 2 = (22, 6√15)` (the `α` end); the partner `T_3` is `tiles[2]` (its edge `2`, traversed from `Q` to `P`), the ONLY
tile other than `tiles[0]` with an edge equal to the chord, and its third vertex `tiles[2].pts 1 = (38, 6√15)` is `P + Q − A`. -/
theorem D44_corner0_chord :
    ∃ P Q : Plane,
      CornerChord D44 (modelAlpha 1 ((2 : ℕ) : ℝ)) (modelBeta 1 ((2 : ℕ) : ℝ))
        (2 * modelAlpha 1 ((2 : ℕ) : ℝ) + modelBeta 1 ((2 : ℕ) : ℝ)) 0 i0 P Q ∧
      P = (D44.tile i0).pts 1 ∧ Q = (D44.tile i0).pts 2 ∧
      (D44.tile i2).edge 2 = segment ℝ P Q ∧ (D44.tile i2).pts 1 = P + Q - D44.target.pts 0 ∧
      ∀ i : Fin Tiling44.tiles.length, i ≠ i0 →
        (∃ k' : Fin 3, (D44.tile i).edge k' = segment ℝ P Q) → i = i2 := by
  obtain ⟨iA, P, Q, hC⟩ :=
    corner_chord_data D44 (by decide) le_rfl (by norm_num) D44_model D44_angleData D44_shape 0 tgt_hb0
  have hA0 : D44.target.pts 0 = (D44.tile i0).pts 0 := D44_same_tgt 0 i0 0 (vtT_0.trans vt0_0.symm)
  have hAmem : D44.target.pts 0 ∈ (D44.tile i0).carrier := by
    rw [hA0]; exact subset_convexHull ℝ _ ⟨0, rfl⟩
  have hiA : iA = i0 := (hC.unique i0 hAmem).symm
  subst hiA
  obtain ⟨j, hjA, hvert⟩ := hC.vertex
  have hj : j = 0 := (D44.tile i0).indep.injective (by rw [← hjA]; exact hA0)
  subst hj
  have hPQ : P = (D44.tile i0).pts 1 ∧ Q = (D44.tile i0).pts 2 := by
    rcases hvert with ⟨hP, hQ⟩ | ⟨hP, hQ⟩
    · exact ⟨hP, hQ⟩
    · exfalso
      have h1 := hC.lenAP
      rw [hP, hA0, model_s0] at h1
      have h2 : dist ((D44.tile i0).pts 0) ((D44.tile i0).pts (0 + 2)) = 32 :=
        D44_dist i0 0 2 1024 32 (by norm_num) d0_02 (by norm_num)
      rw [h2] at h1; norm_num at h1
  obtain ⟨i3, -, huniq⟩ := corner_chord_partner D44_model (by decide) le_rfl (by norm_num) hC
  have h2 : (D44.tile i2).edge 2 = segment ℝ P Q := by
    show segment ℝ ((D44.tile i2).pts 2) ((D44.tile i2).pts (2 + 1)) = _
    rw [show (2 : Fin 3) + 1 = 0 from rfl, hPQ.1, hPQ.2, D44_same i2 i0 2 2 (vt2_2.trans vt0_2.symm),
      D44_same i2 i0 0 1 (vt2_0.trans vt0_1.symm)]
    exact segment_symm ℝ _ _
  have hR : (D44.tile i2).pts 1 = P + Q - D44.target.pts 0 := by
    rw [hPQ.1, hPQ.2, coord_t2_1, coord_t0_1, coord_t0_2, coord_A0]
    ext i
    fin_cases i
    · simp [Erdos634.CertCoord.mkPt_zero]; norm_num
    · simp [Erdos634.CertCoord.mkPt_one]
  refine ⟨P, Q, hC, hPQ.1, hPQ.2, h2, hR, ?_⟩
  rintro i hi ⟨k', hk'⟩
  exact (huniq i ⟨hi, k', hk'⟩).trans (huniq i2 ⟨by decide, 2, h2⟩).symm

/-- **Corner `k = 1`, `A = (176, 0)`, identified.**  The corner tile is `tiles[13]`; `P = tiles[13].pts 0 = (160, 0)`,
`Q = tiles[13].pts 2 = (154, 6√15)`; the partner is `tiles[14]` (its edge `0`), the ONLY tile other than `tiles[13]` with an edge
equal to the chord, and its third vertex `tiles[14].pts 2 = (138, 6√15)` is `P + Q − A`. -/
theorem D44_corner1_chord :
    ∃ P Q : Plane,
      CornerChord D44 (modelAlpha 1 ((2 : ℕ) : ℝ)) (modelBeta 1 ((2 : ℕ) : ℝ))
        (2 * modelAlpha 1 ((2 : ℕ) : ℝ) + modelBeta 1 ((2 : ℕ) : ℝ)) 1 i13 P Q ∧
      P = (D44.tile i13).pts 0 ∧ Q = (D44.tile i13).pts 2 ∧
      (D44.tile i14).edge 0 = segment ℝ P Q ∧ (D44.tile i14).pts 2 = P + Q - D44.target.pts 1 ∧
      ∀ i : Fin Tiling44.tiles.length, i ≠ i13 →
        (∃ k' : Fin 3, (D44.tile i).edge k' = segment ℝ P Q) → i = i14 := by
  obtain ⟨iA, P, Q, hC⟩ :=
    corner_chord_data D44 (by decide) le_rfl (by norm_num) D44_model D44_angleData D44_shape 1 tgt_hb1
  have hA0 : D44.target.pts 1 = (D44.tile i13).pts 1 := D44_same_tgt 1 i13 1 (vtT_1.trans vt13_1.symm)
  have hAmem : D44.target.pts 1 ∈ (D44.tile i13).carrier := by
    rw [hA0]; exact subset_convexHull ℝ _ ⟨1, rfl⟩
  have hiA : iA = i13 := (hC.unique i13 hAmem).symm
  subst hiA
  obtain ⟨j, hjA, hvert⟩ := hC.vertex
  have hj : j = 1 := (D44.tile i13).indep.injective (by rw [← hjA]; exact hA0)
  subst hj
  have hPQ : P = (D44.tile i13).pts 0 ∧ Q = (D44.tile i13).pts 2 := by
    rcases hvert with ⟨hP, hQ⟩ | ⟨hP, hQ⟩
    · exfalso
      have h1 := hC.lenAP
      rw [hP, hA0, model_s0] at h1
      have h2 : dist ((D44.tile i13).pts 1) ((D44.tile i13).pts (1 + 1)) = 32 :=
        D44_dist i13 1 2 1024 32 (by norm_num) d13_12 (by norm_num)
      rw [h2] at h1; norm_num at h1
    · exact ⟨hP, hQ⟩
  obtain ⟨i3, -, huniq⟩ := corner_chord_partner D44_model (by decide) le_rfl (by norm_num) hC
  have h14 : (D44.tile i14).edge 0 = segment ℝ P Q := by
    show segment ℝ ((D44.tile i14).pts 0) ((D44.tile i14).pts (0 + 1)) = _
    rw [show (0 : Fin 3) + 1 = 1 from rfl, hPQ.1, hPQ.2, D44_same i14 i13 0 0 (vt14_0.trans vt13_0.symm),
      D44_same i14 i13 1 2 (vt14_1.trans vt13_2.symm)]
  have hR : (D44.tile i14).pts 2 = P + Q - D44.target.pts 1 := by
    rw [hPQ.1, hPQ.2, coord_t14_2, coord_t13_0, coord_t13_2, coord_A1]
    ext i
    fin_cases i
    · simp [Erdos634.CertCoord.mkPt_zero]; norm_num
    · simp [Erdos634.CertCoord.mkPt_one]
  refine ⟨P, Q, hC, hPQ.1, hPQ.2, h14, hR, ?_⟩
  rintro i hi ⟨k', hk'⟩
  exact (huniq i ⟨hi, k', hk'⟩).trans (huniq i14 ⟨by decide, 0, h14⟩).symm

/-! ## 6. The forward tiles and the forward edges, identified and pinned -/

theorem D44_ident_P0 {X V : Plane} {K : Fin Tiling44.tiles.length}
    (hK : ForwardTile D44 (modelBeta 1 ((2 : ℕ) : ℝ)) X V K) (hX : (D44.tile i1).pts 0 = X) : K = i1 :=
  D44_ident hK i1 0 hX (D44_dist i1 1 2 576 24 (by norm_num) d1_12 (by norm_num))

theorem D44_ident_Q0 {X V : Plane} {K : Fin Tiling44.tiles.length}
    (hK : ForwardTile D44 (modelBeta 1 ((2 : ℕ) : ℝ)) X V K) (hX : (D44.tile i22).pts 0 = X) : K = i22 :=
  D44_ident hK i22 0 hX (D44_dist i22 1 2 576 24 (by norm_num) d22_12 (by norm_num))

theorem D44_ident_P1 {X V : Plane} {K : Fin Tiling44.tiles.length}
    (hK : ForwardTile D44 (modelBeta 1 ((2 : ℕ) : ℝ)) X V K) (hX : (D44.tile i11).pts 1 = X) : K = i11 :=
  D44_ident hK i11 1 hX (D44_dist i11 2 0 576 24 (by norm_num) d11_20 (by norm_num))

theorem D44_ident_Q1 {X V : Plane} {K : Fin Tiling44.tiles.length}
    (hK : ForwardTile D44 (modelBeta 1 ((2 : ℕ) : ℝ)) X V K) (hX : (D44.tile i28).pts 1 = X) : K = i28 :=
  D44_ident hK i28 1 hX (D44_dist i28 2 0 576 24 (by norm_num) d28_20 (by norm_num))

/-- Corner 0, end `P`: the forward tile `tiles[1]` has `P` as its vertex `0`; if the far end `pts m` of its forward edge lies on the
ray from `P` toward the target vertex `1` (the base), then `m = 1`. -/
theorem D44_pin_P0 {m : Fin 3} {t : ℝ} (hm : m = 0 + 1 ∨ m = 0 + 2)
    (hpm : (D44.tile i1).pts m = (D44.tile i1).pts 0 + t • (D44.target.pts 1 - (D44.tile i1).pts 0)) : m = 1 := by
  have hsq : (0 : ℝ) < Real.sqrt 15 := Real.sqrt_pos.mpr (by norm_num)
  rcases hm with rfl | rfl
  · rfl
  · exfalso
    have e02 : (0 : Fin 3) + 2 = 2 := rfl
    rw [e02] at hpm
    have := congrArg (fun x : Plane => x 1) hpm
    simp only [coord_t1_2, coord_t1_0, coord_A1, Erdos634.CertCoord.mkPt_one, PiLp.add_apply, PiLp.smul_apply,
      PiLp.sub_apply, smul_eq_mul] at this
    nlinarith

/-- Corner 0, end `Q`: the forward tile `tiles[22]` has `Q` as its vertex `0`; if the far end `pts m` (`t > 0`) lies on the ray from
`Q` toward the target vertex `2` (the apex), then `m = 2`. -/
theorem D44_pin_Q0 {m : Fin 3} {t : ℝ} (ht : 0 < t) (hm : m = 0 + 1 ∨ m = 0 + 2)
    (hpm : (D44.tile i22).pts m = (D44.tile i22).pts 0 + t • (D44.target.pts 2 - (D44.tile i22).pts 0)) : m = 2 := by
  have hsq : (0 : ℝ) < Real.sqrt 15 := Real.sqrt_pos.mpr (by norm_num)
  rcases hm with rfl | rfl
  · exfalso
    have e01 : (0 : Fin 3) + 1 = 1 := rfl
    rw [e01] at hpm
    have := congrArg (fun x : Plane => x 1) hpm
    simp only [coord_t22_1, coord_t22_0, coord_A2, Erdos634.CertCoord.mkPt_one, PiLp.add_apply, PiLp.smul_apply,
      PiLp.sub_apply, smul_eq_mul] at this
    nlinarith [mul_pos ht hsq]
  · rfl

/-- Corner 1, end `P`: the forward tile `tiles[11]` has `P` as its vertex `1`; if the far end `pts m` lies on the ray from `P`
toward the target vertex `0` (the base), then `m = 0`. -/
theorem D44_pin_P1 {m : Fin 3} {t : ℝ} (hm : m = 1 + 1 ∨ m = 1 + 2)
    (hpm : (D44.tile i11).pts m = (D44.tile i11).pts 1 + t • (D44.target.pts 0 - (D44.tile i11).pts 1)) : m = 0 := by
  have hsq : (0 : ℝ) < Real.sqrt 15 := Real.sqrt_pos.mpr (by norm_num)
  rcases hm with rfl | rfl
  · exfalso
    have e11 : (1 : Fin 3) + 1 = 2 := rfl
    rw [e11] at hpm
    have := congrArg (fun x : Plane => x 1) hpm
    simp only [coord_t11_2, coord_t11_1, coord_A0, Erdos634.CertCoord.mkPt_one, PiLp.add_apply, PiLp.smul_apply,
      PiLp.sub_apply, smul_eq_mul] at this
    nlinarith
  · rfl

/-- Corner 1, end `Q`: the forward tile `tiles[28]` has `Q` as its vertex `1`; if the far end `pts m` (`t > 0`) lies on the ray from
`Q` toward the target vertex `2` (the apex), then `m = 2`. -/
theorem D44_pin_Q1 {m : Fin 3} {t : ℝ} (ht : 0 < t) (hm : m = 1 + 1 ∨ m = 1 + 2)
    (hpm : (D44.tile i28).pts m = (D44.tile i28).pts 1 + t • (D44.target.pts 2 - (D44.tile i28).pts 1)) : m = 2 := by
  have hsq : (0 : ℝ) < Real.sqrt 15 := Real.sqrt_pos.mpr (by norm_num)
  rcases hm with rfl | rfl
  · rfl
  · exfalso
    have e12 : (1 : Fin 3) + 2 = 0 := rfl
    rw [e12] at hpm
    have := congrArg (fun x : Plane => x 1) hpm
    simp only [coord_t28_0, coord_t28_1, coord_A2, Erdos634.CertCoord.mkPt_one, PiLp.add_apply, PiLp.smul_apply,
      PiLp.sub_apply, smul_eq_mul] at this
    nlinarith [mul_pos ht hsq]

/-- The four forward edges of the real tiling have the lengths `16, 32, 32, 16` (`a, c, c, a`). -/
theorem D44_len_P0 : dist ((D44.tile i1).pts 0) ((D44.tile i1).pts 1) = 16 :=
  D44_dist i1 0 1 256 16 (by norm_num) d1_01 (by norm_num)
theorem D44_len_Q0 : dist ((D44.tile i22).pts 0) ((D44.tile i22).pts 2) = 32 :=
  D44_dist i22 0 2 1024 32 (by norm_num) d22_02 (by norm_num)
theorem D44_len_P1 : dist ((D44.tile i11).pts 1) ((D44.tile i11).pts 0) = 32 :=
  D44_dist i11 1 0 1024 32 (by norm_num) d11_10 (by norm_num)
theorem D44_len_Q1 : dist ((D44.tile i28).pts 1) ((D44.tile i28).pts 2) = 16 :=
  D44_dist i28 1 2 256 16 (by norm_num) d28_12 (by norm_num)

end Erdos634.CornerPara.Witness44

#print axioms Erdos634.CornerPara.Witness44.D44_model
#print axioms Erdos634.CornerPara.Witness44.D44_shape
#print axioms Erdos634.CornerPara.Witness44.D44_iso₁
#print axioms Erdos634.CornerPara.Witness44.D44_iso₂
#print axioms Erdos634.CornerPara.Witness44.D44_pts
#print axioms Erdos634.CornerPara.Witness44.D44_tgt_pts
#print axioms Erdos634.CornerPara.Witness44.D44_dist_sq
#print axioms Erdos634.CornerPara.Witness44.D44_dist
#print axioms Erdos634.CornerPara.Witness44.D44_same
#print axioms Erdos634.CornerPara.Witness44.D44_same_tgt
#print axioms Erdos634.CornerPara.Witness44.D44_beta
#print axioms Erdos634.CornerPara.Witness44.D44_ident
#print axioms Erdos634.CornerPara.Witness44.D44_ident_P0
#print axioms Erdos634.CornerPara.Witness44.D44_ident_Q0
#print axioms Erdos634.CornerPara.Witness44.D44_ident_P1
#print axioms Erdos634.CornerPara.Witness44.D44_ident_Q1
#print axioms Erdos634.CornerPara.Witness44.D44_len_P0
#print axioms Erdos634.CornerPara.Witness44.D44_len_Q0
#print axioms Erdos634.CornerPara.Witness44.D44_len_P1
#print axioms Erdos634.CornerPara.Witness44.D44_len_Q1
#print axioms Erdos634.CornerPara.Witness44.D44_corner0_chord
#print axioms Erdos634.CornerPara.Witness44.D44_corner1_chord
#print axioms Erdos634.CornerPara.Witness44.D44_pin_P0
#print axioms Erdos634.CornerPara.Witness44.D44_pin_Q0
#print axioms Erdos634.CornerPara.Witness44.D44_pin_P1
#print axioms Erdos634.CornerPara.Witness44.D44_pin_Q1
