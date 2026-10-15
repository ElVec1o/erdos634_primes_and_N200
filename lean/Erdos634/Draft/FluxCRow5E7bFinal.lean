-- Draft/FluxCRow5E7bFinal.lean: edge direction and character weight, toward the claim that no
-- `c`-edge lies on `∂ABC` (the hypothesis `r = 0`, i.e. `hr0`, of
-- `Row5.sixty_forces_not_gt_three` in `FluxCRow5Complete.lean`).  Imported by `All`.
--
-- The argument for `hr0` has four steps: (1) `Σε = ±N` forces all tile signs `ε` equal
-- (`uniform_sign_pos/_neg`, `FluxCRow5Complete.lean`); (2) by the sign class, every `c`-edge has
-- odd `j`; (3) a tile edge on side `AB`, traversed counterclockwise for its tile, points along `AB`
-- (`j = 0`), likewise `j = 2` on `BC` and `j = 4` on `CA`, all even; (4) hence no `c`-edge lies on
-- `∂ABC`.
--
-- This file treats the geometric content of step (3) at the level the flux machinery uses.
-- `GridChar.weight` (`FluxWeight.lean`) is a function of `Dir.angle`, and
-- `Dir.angle d = Complex.arg (toC d.1)` (`FluxTurn.lean`), the quantity that
-- `FluxCRow5EdgeDirection.lean` equates along collinear points.  The composed result
-- `weight_eq_of_wbtwLeftDir` says: if a positively oriented tile edge starts where a positively
-- oriented target side starts, and the tile edge's far endpoint lies weakly between the side's two
-- endpoints, with the three points pairwise distinct, then every `GridChar` has the same weight on
-- the tile edge's `leftUnit` direction and on the side's `leftUnit` direction.  This is proved for
-- the orientation case `0 < T.det`, `0 < U.det` with tile edge and side both traversed
-- `pts k → pts (k+1)`.
--
-- Not covered: the other three sign combinations of `(0 < T.det, 0 < U.det)`, which need the mirror
-- composition via `arg_eq_of_wbtw_right` or a `Dir.neg` correction; step (2), a separate fact about
-- `wAt`'s values on the model's three labelled edges (`sixty_tileValue_one/two`, `FluxCRow5.lean`)
-- together with the labelling of the model's edges at a placement; and any connection to a
-- `CongruentDissection`: the hypotheses here are pointwise geometric hypotheses on triangles and
-- points, exercised on a concrete numeric witness.  Hence `hr0` is not discharged by this file.
import Erdos634.Draft.FluxCRow5EdgeDirection
import Erdos634.Draft.FluxWeight
import Erdos634.Dissection

namespace Erdos634.Draft.FluxCRow5E7bFinal

open Erdos634.Geometry Erdos634.Draft.FluxCRow5EdgeDirection

/-! ## §1 Positive scalar multiples do not change `Complex.arg ∘ toC`

Pure transport of `Complex.arg_real_mul` (Mathlib) along the linear isometry `toC`. This is what
lets us pass from an arbitrary nonzero edge vector `v - a` (what (L3) is stated for) to its
*normalised* `Dir`, i.e. `Tri.leftUnit`'s actual value (what `GridChar.weight` is stated for). -/

theorem arg_toC_smul_pos {v : Plane} (r : ℝ) (hr : 0 < r) :
    Complex.arg (toC (r • v)) = Complex.arg (toC v) := by
  rw [map_smul, Complex.real_smul]
  exact Complex.arg_real_mul (toC v) hr

/-- `Complex.arg` of a nonzero vector's `toC`-image equals `Complex.arg` of its `leftUnit`-style
normalisation `‖v‖⁻¹ • v`. -/
theorem arg_toC_norm_smul {v : Plane} (hv : v ≠ 0) :
    Complex.arg (toC (‖v‖⁻¹ • v)) = Complex.arg (toC v) :=
  arg_toC_smul_pos (‖v‖⁻¹) (inv_pos.mpr (norm_pos_iff.mpr hv))

/-! ## §2 The `Dir`-level, `Tri.leftUnit`-level form of (L3)

`Tri.leftDir T k` is, by construction (`Dissection.lean:1359`), `T.pts (k+1) - T.pts k` when
`0 < T.det` (the positively-oriented case). `Tri.leftUnit T k` is `‖leftDir k‖⁻¹ • leftDir k`.
Combining §1 with (L3)'s `arg_eq_of_wbtw_left` gives: if the tile's directed edge `k` starts at the
SAME point the target side starts at, and the tile edge's endpoint lies weakly between the side's
two endpoints, the two `leftUnit` directions have equal `Complex.arg ∘ toC`, hence (§3) equal
`Dir.angle`, hence (§4) equal `GridChar.weight` for every `GridChar`. -/

/-- **The positive-orientation case of step (3).** `T`'s edge `k` (positively oriented) shares its
start point with `U`'s edge `j` (also positively oriented), and `T`'s edge endpoint lies weakly
between `U`'s edge endpoints (i.e. `T`'s edge is a sub-segment of `U`'s edge, from the same start
point) — then the two `leftUnit` directions have equal `Complex.arg ∘ toC`. -/
theorem arg_toC_leftUnit_eq_of_wbtw {T U : Tri} {k j : Fin 3}
    (hTpos : 0 < T.det) (hUpos : 0 < U.det)
    (hstart : T.pts k = U.pts j)
    (hwbtw : Wbtw ℝ (U.pts j) (T.pts (k + 1)) (U.pts (j + 1)))
    (hTne : T.pts k ≠ T.pts (k + 1)) (hUne : U.pts j ≠ U.pts (j + 1)) :
    Complex.arg (toC (T.leftUnit k).1) = Complex.arg (toC (U.leftUnit j).1) := by
  have hTdir : T.leftDir k = T.pts (k + 1) - T.pts k := by unfold Tri.leftDir; rw [if_pos hTpos]
  have hUdir : U.leftDir j = U.pts (j + 1) - U.pts j := by unfold Tri.leftDir; rw [if_pos hUpos]
  have hTunit : (T.leftUnit k).1 = ‖T.leftDir k‖⁻¹ • T.leftDir k := rfl
  have hUunit : (U.leftUnit j).1 = ‖U.leftDir j‖⁻¹ • U.leftDir j := rfl
  rw [hTunit, hUunit, hTdir, hUdir]
  rw [arg_toC_norm_smul (sub_ne_zero.mpr (Ne.symm hTne)),
    arg_toC_norm_smul (sub_ne_zero.mpr (Ne.symm hUne))]
  -- rewrite the `Wbtw` hypothesis to the `a v b` shape (L3) expects, using `hstart`
  rw [hstart] at hTne ⊢
  have hwbtw' : Wbtw ℝ (U.pts j) (T.pts (k + 1)) (U.pts (j + 1)) := hwbtw
  have hne1 : U.pts j ≠ T.pts (k + 1) := hTne
  have hne2 : U.pts j ≠ U.pts (j + 1) := hUne
  have := arg_eq_of_wbtw_left hwbtw' hne1 hne2
  rw [← hstart] at this ⊢
  simpa using this

/-! ## §3 Restated at the `Dir.angle` level -/

/-- **Step (3), `Dir.angle` form.** -/
theorem leftUnit_angle_eq_of_wbtw {T U : Tri} {k j : Fin 3}
    (hTpos : 0 < T.det) (hUpos : 0 < U.det)
    (hstart : T.pts k = U.pts j)
    (hwbtw : Wbtw ℝ (U.pts j) (T.pts (k + 1)) (U.pts (j + 1)))
    (hTne : T.pts k ≠ T.pts (k + 1)) (hUne : U.pts j ≠ U.pts (j + 1)) :
    (T.leftUnit k).angle = (U.leftUnit j).angle := by
  unfold Dir.angle
  exact congrArg (fun x : ℝ => (x : Real.Angle))
    (arg_toC_leftUnit_eq_of_wbtw hTpos hUpos hstart hwbtw hTne hUne)

/-! ## §4 Restated at the `GridChar.weight` level — the actual currency of `lem:value`/E7b

`GridChar.weight d = G.val d.angle` (`FluxWeight.lean:85`), a function of `d.angle` alone. Equal
`Dir.angle` therefore forces equal `weight`, FOR EVERY `GridChar`, without knowing anything about
`G.L`/`G.ψ`/the anchor. This is the exact form step (3) needs to feed step (4)'s uniform-sign
argument: a tile edge lying on a target side has the SAME weight as the side itself, for whichever
`GridChar` E7b's argument is running (`wAt α hα 0 anc`, `FluxCRow5.lean`). -/

/-- **(L4)'s edge-to-weight bridge, one orientation case.** -/
theorem weight_eq_of_wbtwLeftDir {T U : Tri} {k j : Fin 3}
    (hTpos : 0 < T.det) (hUpos : 0 < U.det)
    (hstart : T.pts k = U.pts j)
    (hwbtw : Wbtw ℝ (U.pts j) (T.pts (k + 1)) (U.pts (j + 1)))
    (hTne : T.pts k ≠ T.pts (k + 1)) (hUne : U.pts j ≠ U.pts (j + 1))
    {R : Type*} [CommRing R] (G : GridChar R) :
    G.weight (T.leftUnit k) = G.weight (U.leftUnit j) := by
  unfold GridChar.weight
  exact congrArg G.val (leftUnit_angle_eq_of_wbtw hTpos hUpos hstart hwbtw hTne hUne)

end Erdos634.Draft.FluxCRow5E7bFinal

/-! ## §5 Non-vacuous witness

A concrete pair of positively-oriented triangles `T` (a small tile edge) and `U` (the "target side",
here just another triangle whose edge `0` is the long segment) with `T`'s edge `0` a genuine
sub-segment of `U`'s edge `0` from the same start point, all hypotheses non-trivially satisfied, and
the conclusion (`weight` agreement) exercised on an arbitrary `GridChar` (the theorem holds for
every one, so exhibiting the hypotheses' joint satisfiability is what the witness must show).
Built via `Erdos634.CertCoord.mkTri`, the corpus's own coordinate-to-`Tri` dictionary
(`CertCoord.lean`), rather than a bespoke `AffineIndependent` proof. -/
section Witness

open Erdos634.Geometry Erdos634.CertCoord Erdos634.Draft.FluxCRow5E7bFinal

/-- The small tile: `(0,0) → (1,0) → (0,1)`, `det3 = 1 ≠ 0`. -/
theorem wT_hdet : Erdos634.CertCoord.det3 0 0 1 0 0 1 ≠ 0 := by unfold det3; norm_num

/-- The "target": `(0,0) → (3,0) → (0,1)`, `det3 = 3 ≠ 0`. -/
theorem wU_hdet : Erdos634.CertCoord.det3 0 0 3 0 0 1 ≠ 0 := by unfold det3; norm_num

noncomputable def wT : Tri := mkTri 0 0 1 0 0 1 wT_hdet
noncomputable def wU : Tri := mkTri 0 0 3 0 0 1 wU_hdet

theorem wT_pts0 : wT.pts 0 = mkPt 0 0 := by simp [wT, mkTri_pts]
theorem wT_pts1 : wT.pts 1 = mkPt 1 0 := by simp [wT, mkTri_pts]
theorem wT_pts2 : wT.pts 2 = mkPt 0 1 := by simp [wT, mkTri_pts]
theorem wU_pts0 : wU.pts 0 = mkPt 0 0 := by simp [wU, mkTri_pts]
theorem wU_pts1 : wU.pts 1 = mkPt 3 0 := by simp [wU, mkTri_pts]
theorem wU_pts2 : wU.pts 2 = mkPt 0 1 := by simp [wU, mkTri_pts]

theorem wT_det_pos : 0 < wT.det := by
  unfold Tri.det
  rw [wT_pts0, wT_pts1, wT_pts2]
  simp only [PiLp.sub_apply, mkPt_zero, mkPt_one]
  norm_num

theorem wU_det_pos : 0 < wU.det := by
  unfold Tri.det
  rw [wU_pts0, wU_pts1, wU_pts2]
  simp only [PiLp.sub_apply, mkPt_zero, mkPt_one]
  norm_num

theorem wstart : wT.pts 0 = wU.pts 0 := by rw [wT_pts0, wU_pts0]

theorem wwbtw : Wbtw ℝ (wU.pts 0) (wT.pts 1) (wU.pts 1) := by
  rw [wU_pts0, wT_pts1, wU_pts1]
  exact witness_wbtw

theorem wTne : wT.pts 0 ≠ wT.pts 1 := by
  rw [wT_pts0, wT_pts1]; exact witness_ne_av

theorem wUne : wU.pts 0 ≠ wU.pts 1 := by
  rw [wU_pts0, wU_pts1]; exact witness_ne_ab

/-- **The witness fires**: for this genuinely-satisfied, non-degenerate instance, the small edge
(`(0,0)→(1,0)`, a sub-segment of the target side) and the big edge (`(0,0)→(3,0)`) have equal
weight under EVERY `GridChar` — the conclusion is non-trivial (the two edges are geometrically
distinct segments) and the hypotheses are jointly satisfiable, exhibited here concretely. -/
theorem witness_weight_eq {R : Type*} [CommRing R] (G : GridChar R) :
    G.weight (wT.leftUnit 0) = G.weight (wU.leftUnit 0) :=
  Erdos634.Draft.FluxCRow5E7bFinal.weight_eq_of_wbtwLeftDir
    wT_det_pos wU_det_pos wstart wwbtw wTne wUne G

end Witness

#print axioms Erdos634.Draft.FluxCRow5E7bFinal.arg_toC_smul_pos
#print axioms Erdos634.Draft.FluxCRow5E7bFinal.arg_toC_norm_smul
#print axioms Erdos634.Draft.FluxCRow5E7bFinal.arg_toC_leftUnit_eq_of_wbtw
#print axioms Erdos634.Draft.FluxCRow5E7bFinal.leftUnit_angle_eq_of_wbtw
#print axioms Erdos634.Draft.FluxCRow5E7bFinal.weight_eq_of_wbtwLeftDir
#print axioms wT_det_pos
#print axioms wU_det_pos
#print axioms witness_weight_eq
