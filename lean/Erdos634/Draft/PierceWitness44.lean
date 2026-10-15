import Erdos634.Draft.PierceRung2
import Erdos634.Draft.ApexWitness44
import Erdos634.Realizable

/-!
# The hypotheses of `thm:pierce` and `prop:rung2` hold on a real tiling  `PierceScale.thm_pierce_scale` and `PierceRung2.rung2` (the pierced corner and
rung two of the pierce analysis, at every scale) take the hypothesis
`ApexPlacement.LegFlanksC D k c`: every tile edge at the apex that lies along a leg has length
`c`.  At scale one it follows from the absence of `b`-edges on the legs, but no tiling exists at
scale one; so until now the hypothesis was not exhibited on any tiling in Lean
(`ApexWitness44`'s header: "true there by inspection of tiles #41–43, … but not formalized").

Here it is exhibited on the kernel-checked 44-tiling, the member `(1,2)` at scale `2`.

* `flank_table` : a `decide` check on the certificate's integer data: a vertex of a tile that is
  collinear with the apex and a base corner, in a tile having a vertex at the apex, is at squared
  distance `1024 = 32²` from the apex.
* `D44s` : the 44-tiling scaled by `1/8`, so that the tile is `(2, 3, 4)` and the target
  `(16, 16, 22)`.
* `modelData44`, `corner44`, `legFlanks44` : `ModelDataE D44s 1 2 α β γ`, the apex corner `3α`, and
  `LegFlanksC D44s 2 4`.
* `pierce44` : the conclusion of `thm_pierce_scale` for `D44s` (the pierced corner exists in the
  44-tiling).

Standard axioms, no `sorry`.
-/

open scoped Classical
open Erdos634 Erdos634.Geometry Erdos634.Z15Real Erdos634.Tiling44Bridge
  Erdos634.BaseBetaTargetCoord Erdos634.CertCoord Erdos634.TilePlacement
open Erdos634.Draft.ApexPlacement Erdos634.Draft.ApexWitness44 Erdos634.Realizable

namespace Erdos634.Draft.PierceWitness44

/-! ## The integer table -/

/-- `z.1² = 15·z.2²`: the only way `z.1 + z.2·√15` can vanish. -/
def pz (z : Tiling44.Z15) : Bool := z.1 ^ 2 == 15 * z.2 ^ 2

theorem pz_of_toR_zero {z : Z15} (h : toR z = 0) : pz z = true := by
  by_contra hne
  have h' : z.1 ^ 2 ≠ 15 * z.2 ^ 2 := by
    intro heq
    apply hne
    simp [pz, heq]
  exact toR_ne_zero_of_sq_ne h' h

/-- The apex of the target of the certificate. -/
def apexZ : Tiling44.Pt := Tiling44.t3 Tiling44.target

/-- **The table.**  In a tile with a vertex `m` at the apex, another vertex `m'` that is collinear
with the apex and a base corner of the target is at squared distance `1024` from the apex. -/
theorem flank_table : ∀ t ∈ Tiling44.tiles, ∀ m m' : Fin 3, m' ≠ m →
    pz (Tiling44.zsub (Tiling44.px (vertexOf t m)) (Tiling44.px apexZ)) = true →
    pz (Tiling44.zsub (Tiling44.py (vertexOf t m)) (Tiling44.py apexZ)) = true →
    ∀ L ∈ [Tiling44.t1 Tiling44.target, Tiling44.t2 Tiling44.target],
      pz (Tiling44.cross apexZ L (vertexOf t m')) = true →
      Tiling44.dist2 apexZ (vertexOf t m') = ((1024 : ℤ), (0 : ℤ)) := by
  decide

/-! ## The scaled tiling -/

theorem h8 : (1 / 8 : ℝ) ≠ 0 := by norm_num

/-- The 44-tiling scaled by `1/8`: tile `(2, 3, 4)`, target `(16, 16, 22)`. -/
noncomputable def D44s : CongruentDissection Tiling44.tiles.length :=
  scaleDissection 0 (1 / 8) h8 D44

theorem hom_apply (x : Plane) : homothetyEquiv 0 (1 / 8) h8 x = (1 / 8 : ℝ) • x := by
  rw [homothetyEquiv_apply, AffineMap.homothety_apply]
  simp

theorem D44s_target (k : Fin 3) : D44s.target.pts k = (1 / 8 : ℝ) • D44.target.pts k := by
  rw [← hom_apply]; rfl

theorem D44s_model (k : Fin 3) : D44s.model.pts k = (1 / 8 : ℝ) • D44.model.pts k := by
  rw [← hom_apply]; rfl

theorem D44s_tile (i : Fin Tiling44.tiles.length) (m : Fin 3) :
    (D44s.tile i).pts m = (1 / 8 : ℝ) • (D44.tile i).pts m := by
  rw [← hom_apply]; rfl

theorem dist_scaled (x y : Plane) : dist ((1 / 8 : ℝ) • x) ((1 / 8 : ℝ) • y) = dist x y / 8 := by
  rw [dist_smul₀, Real.norm_of_nonneg (by norm_num)]; ring

theorem angle_scaled (x y z : Plane) :
    cornerAngle ((1 / 8 : ℝ) • x) ((1 / 8 : ℝ) • y) ((1 / 8 : ℝ) • z) = cornerAngle x y z := by
  unfold cornerAngle EuclideanGeometry.angle
  rw [vsub_eq_sub, vsub_eq_sub, vsub_eq_sub, vsub_eq_sub, ← smul_sub, ← smul_sub]
  exact InnerProductGeometry.angle_smul_smul h8 _ _

/-- The model data of the scaled tiling: sides `(2, 3, 4) = (e f, f² − e², f²)` at `(1, 2)`. -/
theorem modelData44 :
    Erdos634.Draft.HalfTurnR3R4Glue.ModelDataE D44s ((1 : ℕ) : ℝ) ((2 : ℕ) : ℝ)
      (modelAlpha 1 ((2 : ℕ) : ℝ)) (modelBeta 1 ((2 : ℕ) : ℝ))
      (2 * modelAlpha 1 ((2 : ℕ) : ℝ) + modelBeta 1 ((2 : ℕ) : ℝ)) where
  hs0 := by
    show dist (D44s.model.pts 1) (D44s.model.pts 2) = _
    rw [D44s_model, D44s_model, dist_scaled]
    have : dist (D44.model.pts 1) (D44.model.pts 2) = 16 := piece_d01
    rw [this]; norm_num
  hs1 := by
    show dist (D44s.model.pts 2) (D44s.model.pts 0) = _
    rw [D44s_model, D44s_model, dist_scaled]
    have : dist (D44.model.pts 2) (D44.model.pts 0) = 24 := piece_d12
    rw [this]; norm_num
  hs2 := by
    show dist (D44s.model.pts 0) (D44s.model.pts 1) = _
    rw [D44s_model, D44s_model, dist_scaled]
    have : dist (D44.model.pts 0) (D44.model.pts 1) = 32 := piece_d20
    rw [this]; norm_num
  hα' := by rw [D44s_model, D44s_model, D44s_model, angle_scaled]; exact D44_hα
  hβ' := by rw [D44s_model, D44s_model, D44s_model, angle_scaled]; exact D44_hβ
  hγ' := by rw [D44s_model, D44s_model, D44s_model, angle_scaled]; exact D44_hγ

/-- The apex corner of the scaled target is `3α`. -/
theorem corner44 : cornerAngle (D44s.target.pts (2 + 1)) (D44s.target.pts 2)
    (D44s.target.pts (2 + 2)) = 3 * modelAlpha 1 ((2 : ℕ) : ℝ) := by
  rw [D44s_target, D44s_target, D44s_target, angle_scaled]; exact D44_hcorner

/-! ## The apex flanks along the legs are `c` -/

theorem target_pt (k : Fin 3) : D44.target.pts k = mkPt
    (toR (zx (toZPt (![Tiling44.t1 Tiling44.target, Tiling44.t2 Tiling44.target,
      Tiling44.t3 Tiling44.target] k))))
    (toR (zy (toZPt (![Tiling44.t1 Tiling44.target, Tiling44.t2 Tiling44.target,
      Tiling44.t3 Tiling44.target] k)))) :=
  targetTri_pts_eq k

theorem tile_pt (i : Fin Tiling44.tiles.length) (j : Fin 3) :
    (D44.tile i).pts j = mkPt (toR (zx (toZPt (vertexOf (Tiling44.tiles[i.val]) j))))
      (toR (zy (toZPt (vertexOf (Tiling44.tiles[i.val]) j)))) :=
  pieceTri_pts _ (List.getElem_mem i.isLt) j

theorem mkPt_inj' {a b c d : ℝ} (h : mkPt a b = mkPt c d) : a = c ∧ b = d :=
  ⟨by have := congrArg (fun p : Plane => p 0) h; simpa using this,
   by have := congrArg (fun p : Plane => p 1) h; simpa using this⟩

theorem fin3_p1 (m : Fin 3) : m + 1 ≠ m := by revert m; decide
theorem fin3_p2 (m : Fin 3) : m + 2 ≠ m := by revert m; decide
theorem fin3_01 (l : Fin 3) (h : l ≠ 2) : l = 0 ∨ l = 1 := by revert l; decide

/-- **`LegFlanksC` on the 44-tiling.** -/
theorem legFlanks44 : LegFlanksC D44s 2 (((2 : ℕ) : ℝ) ^ 2) := by
  intro i m U W l S hvm hfl hl hS hdir
  -- the flank vertex
  obtain ⟨m', hm', hU⟩ : ∃ m' : Fin 3, m' ≠ m ∧ U = (D44s.tile i).pts m' - D44s.target.pts 2 := by
    rcases hfl with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact ⟨m + 1, fin3_p1 m, h1⟩
    · exact ⟨m + 2, fin3_p2 m, h1⟩
  -- unscale the three facts
  rw [D44s_tile, D44s_target] at hvm
  have hvm' : (D44.tile i).pts m = D44.target.pts 2 := smul_right_injective Plane h8 hvm
  rw [D44s_tile, D44s_target] at hU
  have hU' : U = (1 / 8 : ℝ) • ((D44.tile i).pts m' - D44.target.pts 2) := by
    rw [hU, smul_sub]
  rw [D44s_target, D44s_target, hU', ← smul_sub, smul_comm] at hdir
  have hdir' : D44.target.pts l - D44.target.pts 2
      = S • ((D44.tile i).pts m' - D44.target.pts 2) := smul_right_injective Plane h8 hdir
  -- coordinates
  set t := Tiling44.tiles[i.val] with ht
  have htm : t ∈ Tiling44.tiles := List.getElem_mem i.isLt
  have hA : D44.target.pts 2 = mkPt (toR (zx (toZPt apexZ))) (toR (zy (toZPt apexZ))) :=
    target_pt 2
  rw [tile_pt i m, hA] at hvm'
  obtain ⟨hx, hy⟩ := mkPt_inj' hvm'
  have pzx : pz (Tiling44.zsub (Tiling44.px (vertexOf t m)) (Tiling44.px apexZ)) = true := by
    apply pz_of_toR_zero
    show toR (zsub (zx (toZPt (vertexOf t m))) (zx (toZPt apexZ))) = 0
    rw [toR_sub]; linarith
  have pzy : pz (Tiling44.zsub (Tiling44.py (vertexOf t m)) (Tiling44.py apexZ)) = true := by
    apply pz_of_toR_zero
    show toR (zsub (zy (toZPt (vertexOf t m))) (zy (toZPt apexZ))) = 0
    rw [toR_sub]; linarith
  -- the leg end
  obtain ⟨L, hL, hLpt⟩ : ∃ L ∈ [Tiling44.t1 Tiling44.target, Tiling44.t2 Tiling44.target],
      D44.target.pts l = mkPt (toR (zx (toZPt L))) (toR (zy (toZPt L))) := by
    have hl' : l = 0 ∨ l = 1 := fin3_01 l hl
    rcases hl' with rfl | rfl
    · exact ⟨Tiling44.t1 Tiling44.target, by simp, target_pt 0⟩
    · exact ⟨Tiling44.t2 Tiling44.target, by simp, target_pt 1⟩
  -- collinearity
  have pzc : pz (Tiling44.cross apexZ L (vertexOf t m')) = true := by
    apply pz_of_toR_zero
    show toR (zcross (toZPt apexZ) (toZPt L) (toZPt (vertexOf t m'))) = 0
    rw [← toR_zcross]
    rw [hLpt, hA, tile_pt i m'] at hdir'
    have h0 := congrArg (fun p : Plane => p 0) hdir'
    have h1 := congrArg (fun p : Plane => p 1) hdir'
    simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, mkPt_zero, mkPt_one] at h0 h1
    unfold det3
    rw [h0, h1]; ring
  have hd := flank_table t htm m m' hm' pzx pzy L hL pzc
  -- back to the reals
  have hdist : dist ((D44.tile i).pts m') (D44.target.pts 2) = 32 := by
    apply Erdos634.Draft.ApexWitness44.dist_of_sq (v := 1024) (by norm_num) _ (by norm_num)
    rw [tile_pt i m', hA, dist_comm, dist_sq_mkPt]
    have := toR_zdist2 (toZPt apexZ) (toZPt (vertexOf t m'))
    rw [this]
    have hd' : zdist2 (toZPt apexZ) (toZPt (vertexOf t m')) = ((1024 : ℤ), (0 : ℤ)) := hd
    rw [hd']; simp [toR]
  rw [hU', norm_smul, Real.norm_of_nonneg (by norm_num), ← dist_eq_norm, hdist]
  norm_num

/-! ## The witness -/

theorem angleData44 : MarchSlots.AngleData (modelAlpha 1 ((2 : ℕ) : ℝ)) (modelBeta 1 ((2 : ℕ) : ℝ))
    (2 * modelAlpha 1 ((2 : ℕ) : ℝ) + modelBeta 1 ((2 : ℕ) : ℝ)) := D44_angleData

/-- **The frame of `PierceScale` exists on the 44-tiling**: every hypothesis of
`PierceScale.exists_sframe`, hence of `thm_pierce_scale` and of `PierceRung2.rung2`, holds for the
real dissection `D44s`. -/
theorem sframe44 : Nonempty (Erdos634.Draft.PierceScale.SFrame D44s 1 2
    (modelAlpha 1 ((2 : ℕ) : ℝ)) (modelBeta 1 ((2 : ℕ) : ℝ))
    (2 * modelAlpha 1 ((2 : ℕ) : ℝ) + modelBeta 1 ((2 : ℕ) : ℝ)) 2) :=
  Erdos634.Draft.PierceScale.exists_sframe D44s (by decide) le_rfl (by norm_num) modelData44
    angleData44 2 corner44 legFlanks44

end Erdos634.Draft.PierceWitness44
