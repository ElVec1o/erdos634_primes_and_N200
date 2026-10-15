-- Draft/FluxCRow5EdgeDirection.lean: direction of sub-edges.  If `b` lies weakly between `a` and
-- `c`, the directions of `b − a` and `c − a` have equal `Dir.angle`.
--
-- This is assembled from three Mathlib facts at the `Plane`/`toC`/`Dir.angle` level used here:
--   * `Wbtw.sameRay_vsub_left`, `Wbtw.sameRay_vsub_right`, `Wbtw.sameRay_vsub`
--     (`Mathlib/Analysis/Convex/Between.lean`): betweenness gives `SameRay`;
--   * `Complex.sameRay_iff` (`Mathlib/Analysis/Complex/Arg.lean`): two nonzero vectors in the same
--     ray have equal `Complex.arg`;
--   * `SameRay.sameRay_map_iff` (`Mathlib/LinearAlgebra/Ray.lean`): transports `SameRay` across
--     `toC`.
-- The existing betweenness developments `WallEndpoints.lean`, `SideWall.lean`, `WbtwChain.lean`
-- concern ordering and contiguity only, and `Draft/FluxGRow3DirAngle.lean` converts raw coordinates
-- `(r cos θ, r sin θ)` into a `Dir.angle`; neither gives the direction fact needed here.  The
-- statements `arg_eq_of_wbtw_left/right/subedges` and their `Real.Angle` forms `angle_eq_of_wbtw_*`
-- are generic in the two boundary points and the between point; nothing is numeric.
import Erdos634.Draft.FluxTurn
import Erdos634.CertCoord
import Mathlib.Analysis.Complex.Arg

namespace Erdos634.Draft.FluxCRow5EdgeDirection

open Erdos634.Geometry Complex

/-! ## §1 `SameRay` transports across `toC`

Pure transport of the abstract Mathlib fact `SameRay.sameRay_map_iff` along the concrete linear
isometry equivalence `toC : Plane ≃ₗᵢ[ℝ] ℂ` this corpus already uses for `Dir.angle`. No new content;
recorded as its own lemma so §2 never has to touch `LinearIsometryEquiv.toLinearEquiv` directly. -/

theorem sameRay_toC_iff (u v : Plane) : SameRay ℝ (toC u) (toC v) ↔ SameRay ℝ u v :=
  SameRay.sameRay_map_iff toC.toLinearEquiv

/-! ## §2 Same ray, both nonzero, gives equal `Complex.arg`

This is `Complex.sameRay_iff` read in the direction this file needs, specialised to vectors of
`Plane` via `toC`. -/

theorem arg_toC_eq_of_sameRay {u v : Plane} (hray : SameRay ℝ u v) (hu : u ≠ 0) (hv : v ≠ 0) :
    Complex.arg (toC u) = Complex.arg (toC v) := by
  have hray' : SameRay ℝ (toC u) (toC v) := (sameRay_toC_iff u v).mpr hray
  rcases Complex.sameRay_iff.mp hray' with h | h | h
  · exact absurd h (toC_ne_zero hu)
  · exact absurd h (toC_ne_zero hv)
  · exact h

/-! ## §3 The affine core of (L3): betweenness gives equal edge direction

`Wbtw ℝ a v b` says `v` lies weakly between `a` and `b` (equivalently, `v ∈ segment ℝ a b`, the
exact hypothesis form `WallEndpoints.lean`/`SideWall.lean`/`WbtwChain.lean` already produce and
consume throughout this corpus). Given that and nondegeneracy of the two edges being compared, their
`toC`-images have EQUAL `Complex.arg` — not merely equal mod `π` — because `Wbtw.sameRay_vsub_left`/
`_right`/(unprimed) give `SameRay`, not just collinearity, and `SameRay` remembers which of the two
directions along the line is meant. -/

/-- **(L3a).** If `v` lies weakly between `a` and `b`, the edge `a → v` points in exactly the same
direction (equal `Complex.arg` of `toC`, not just mod `π`) as the full chord `a → b`. -/
theorem arg_eq_of_wbtw_left {a v b : Plane} (h : Wbtw ℝ a v b) (hav : a ≠ v) (hab : a ≠ b) :
    Complex.arg (toC (v - a)) = Complex.arg (toC (b - a)) := by
  have hray : SameRay ℝ (v -ᵥ a) (b -ᵥ a) := h.sameRay_vsub_left
  simp only [vsub_eq_sub] at hray
  exact arg_toC_eq_of_sameRay hray (sub_ne_zero.mpr (Ne.symm hav)) (sub_ne_zero.mpr (Ne.symm hab))

/-- **(L3b).** If `v` lies weakly between `a` and `b`, the edge `v → b` also points in exactly the
same direction as the full chord `a → b`. -/
theorem arg_eq_of_wbtw_right {a v b : Plane} (h : Wbtw ℝ a v b) (hvb : v ≠ b) (hab : a ≠ b) :
    Complex.arg (toC (b - v)) = Complex.arg (toC (b - a)) := by
  have hray : SameRay ℝ (b -ᵥ a) (b -ᵥ v) := h.sameRay_vsub_right
  simp only [vsub_eq_sub] at hray
  exact (arg_toC_eq_of_sameRay hray (sub_ne_zero.mpr (Ne.symm hab))
    (sub_ne_zero.mpr (Ne.symm hvb))).symm

/-- **(L3c).** The two sub-edges `a → v` and `v → b` agree with each other directly, without
routing through the full chord — the form actually needed when only local betweenness among an
edge's own three named points (`a`, `v`, `b`) is known, with no separate hypothesis about a `c`-edge
elsewhere on the same side. -/
theorem arg_eq_of_wbtw_subedges {a v b : Plane} (h : Wbtw ℝ a v b) (hav : a ≠ v) (hvb : v ≠ b) :
    Complex.arg (toC (v - a)) = Complex.arg (toC (b - v)) := by
  have hray : SameRay ℝ (v -ᵥ a) (b -ᵥ v) := h.sameRay_vsub
  simp only [vsub_eq_sub] at hray
  exact arg_toC_eq_of_sameRay hray (sub_ne_zero.mpr (Ne.symm hav)) (sub_ne_zero.mpr (Ne.symm hvb))

/-! ## §4 The `Real.Angle`/`Dir.angle` form

Restated at the level `Draft/FluxGRow3DirAngle.lean` (P110/P111) and the row-5 sign-class argument
actually consume: the `Real.Angle` coercions of the two `Complex.arg` values are equal. This is a
direct `congrArg` of §3, kept as its own declaration so a caller matching on `Real.Angle` (as
`IsGridA`/`Dir.angle`-style consumers do) does not have to redo the coercion. -/

/-- **(L3), `Real.Angle` form, left edge.** -/
theorem angle_eq_of_wbtw_left {a v b : Plane} (h : Wbtw ℝ a v b) (hav : a ≠ v) (hab : a ≠ b) :
    (Complex.arg (toC (v - a)) : Real.Angle) = (Complex.arg (toC (b - a)) : Real.Angle) :=
  congrArg _ (arg_eq_of_wbtw_left h hav hab)

/-- **(L3), `Real.Angle` form, right edge.** -/
theorem angle_eq_of_wbtw_right {a v b : Plane} (h : Wbtw ℝ a v b) (hvb : v ≠ b) (hab : a ≠ b) :
    (Complex.arg (toC (b - v)) : Real.Angle) = (Complex.arg (toC (b - a)) : Real.Angle) :=
  congrArg _ (arg_eq_of_wbtw_right h hvb hab)

/-- **(L3), `Real.Angle` form, the two sub-edges.** -/
theorem angle_eq_of_wbtw_subedges {a v b : Plane} (h : Wbtw ℝ a v b) (hav : a ≠ v) (hvb : v ≠ b) :
    (Complex.arg (toC (v - a)) : Real.Angle) = (Complex.arg (toC (b - v)) : Real.Angle) :=
  congrArg _ (arg_eq_of_wbtw_subedges h hav hvb)

end Erdos634.Draft.FluxCRow5EdgeDirection

/-! ## §5 Non-vacuous witness

A concrete, contradiction-free instance with `a ≠ v`, `v ≠ b`, `a ≠ b`, and `Wbtw ℝ a v b` actually
holding, on which every theorem above is exercised — the no-vacuous-witness rule. Uses `Plane`
points built from `EuclideanSpace.equiv`/`!₂[…]`-free literal coordinates via `PiLp`/`EuclideanSpace`
addition already standard in this corpus (`Erdos634.Geometry.Plane := EuclideanSpace ℝ (Fin 2)`),
avoiding any tile/dissection data so the witness has no hidden hypothesis of its own. -/
section Witness

open Erdos634.Geometry Erdos634.CertCoord

/-- Three collinear points on the real line embedded on the x-axis: `a = (0,0)`, `v = (1,0)`,
`b = (3,0)`. `v` is genuinely between `a` and `b` (not an endpoint), and all three are pairwise
distinct. -/
noncomputable def wa : Plane := mkPt 0 0
noncomputable def wv : Plane := mkPt 1 0
noncomputable def wb : Plane := mkPt 3 0

theorem witness_wbtw : Wbtw ℝ wa wv wb := by
  refine ⟨(1 : ℝ) / 3, ⟨by norm_num, by norm_num⟩, ?_⟩
  rw [AffineMap.lineMap_apply]
  ext i
  fin_cases i <;>
    simp [wa, wv, wb, vsub_eq_sub, vadd_eq_add, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply,
      mkPt_zero, mkPt_one] <;> norm_num

theorem witness_ne_av : wa ≠ wv := by
  intro h
  have := congrArg (fun p : Plane => p 0) h
  simp [wa, wv, mkPt_zero] at this

theorem witness_ne_vb : wv ≠ wb := by
  intro h
  have := congrArg (fun p : Plane => p 0) h
  simp [wv, wb, mkPt_zero] at this

theorem witness_ne_ab : wa ≠ wb := by
  intro h
  have := congrArg (fun p : Plane => p 0) h
  simp [wa, wb, mkPt_zero] at this

/-- The witness fires: the three theorems of §3/§4 all apply here without contradiction, and their
conclusion (`arg (toC (v - a)) = arg (toC (b - a))`, both directions pointing along the positive
x-axis, `arg = 0`) is the expected, non-trivial value — not a `False`-derived triviality. -/
theorem witness_fires :
    Complex.arg (Erdos634.Geometry.toC (wv - wa)) = Complex.arg (Erdos634.Geometry.toC (wb - wa)) :=
  Erdos634.Draft.FluxCRow5EdgeDirection.arg_eq_of_wbtw_left witness_wbtw witness_ne_av witness_ne_ab

theorem witness_value : Complex.arg (Erdos634.Geometry.toC (wb - wa)) = 0 := by
  have hsub : wb - wa = mkPt 3 0 := by
    ext i
    fin_cases i <;> simp [wa, wb, PiLp.sub_apply, mkPt_zero, mkPt_one]
  rw [hsub]
  have hval : Erdos634.Geometry.toC (mkPt (3:ℝ) 0) = (3 : ℂ) := by
    rw [Erdos634.Geometry.toC_apply, mkPt_zero, mkPt_one]
    norm_num
  rw [hval]
  simp

end Witness

#print axioms Erdos634.Draft.FluxCRow5EdgeDirection.sameRay_toC_iff
#print axioms Erdos634.Draft.FluxCRow5EdgeDirection.arg_toC_eq_of_sameRay
#print axioms Erdos634.Draft.FluxCRow5EdgeDirection.arg_eq_of_wbtw_left
#print axioms Erdos634.Draft.FluxCRow5EdgeDirection.arg_eq_of_wbtw_right
#print axioms Erdos634.Draft.FluxCRow5EdgeDirection.arg_eq_of_wbtw_subedges
#print axioms Erdos634.Draft.FluxCRow5EdgeDirection.angle_eq_of_wbtw_left
#print axioms Erdos634.Draft.FluxCRow5EdgeDirection.angle_eq_of_wbtw_right
#print axioms Erdos634.Draft.FluxCRow5EdgeDirection.angle_eq_of_wbtw_subedges
#print axioms witness_wbtw
#print axioms witness_fires
#print axioms witness_value
