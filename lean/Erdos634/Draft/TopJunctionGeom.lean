import Erdos634.Draft.ColumnLinesGeom
import Erdos634.ChordChartPlanar

/-!
# The filler endpoint at the top junction against the right side

Two points are tested against the right side of the `m = 1` target of the member `(1,f)`: with `J = (f−1)·c·u` the last junction of
the left side (the side word ends with one `c`), the points `J + (c,0)` (mirrored filler) and
`J + (b,0)` (direct filler), `c = f²`, `b = f² − 1`.  The test reduces,
exactly, to the signs of `f³ − 3f² + 1` and `f³ − 3f² − f + 1`.  That reduction, and both
directions of each equivalence, are proved here in the coordinates of
`BaseBetaTargetCoord.baseBetaTarget 1 f`.

* `rightFunctional_carrier` : on the target, `(L − x)·H − (L/2)·y ≥ 0` (the right side's functional).
* `right_mirrored`, `right_direct` : the value of that functional at the two points is
  `−H(f³ − 3f² + 1)/f` and `−H(f³ − 3f² − f + 1)/f`.
* `mirrored_outside`, `mirrored_inside` and `direct_outside`, `direct_inside` : the point is outside
  the target when the polynomial is positive and interior to it when the polynomial is negative
  (real `f > 1`).
* `mirrored_outside_iff`, `direct_outside_iff` : for a natural number `f ≥ 2`, the point is outside
  the target iff the polynomial is positive iff `f ≥ 3`, respectively `f ≥ 4`.

No statement here is about a tiling.  Standard axioms, no `sorry`.
-/

namespace Erdos634.Draft.TopJunctionGeom

open Erdos634 Erdos634.Geometry Erdos634.CertCoord Erdos634.BaseBetaTargetCoord
open Erdos634.Draft.ColumnLinesGeom

/-- The last junction of the left side, `J = (f−1)·c·u`, as coordinates. -/
noncomputable def Jx (f : ℝ) : ℝ := (f - 1) * (sideA 1 f).1
noncomputable def Jy (f : ℝ) : ℝ := (f - 1) * (sideA 1 f).2

/-- `J` is the lattice vertex `(f−1)·c·u`. -/
theorem J_eq (f : ℝ) : mkPt (Jx f) (Jy f) = lat 1 f 0 (f - 1) := by
  apply plane_ext
  · rw [lat_zero, mkPt_zero, Jx]; ring
  · rw [lat_one, mkPt_one, Jy]

/-- The right side's linear functional is nonnegative on the target. -/
theorem rightFunctional_carrier {e f : ℝ} (he : 0 < e) (hef : e < f) :
    ∀ q : Plane, q ∈ (baseBetaTarget e f he hef).carrier →
      0 ≤ (baseLen e f - q 0) * height e f - baseLen e f / 2 * q 1 := by
  have hH := height_pos he hef
  have hL := baseLen_pos he hef
  have hconv : Convex ℝ {q : Plane | 0 ≤ (baseLen e f - q 0) * height e f - baseLen e f / 2 * q 1} := by
    intro x hx y hy a b ha hb hab
    simp only [Set.mem_setOf_eq] at hx hy ⊢
    have hx0 : (a • x + b • y) 0 = a * x 0 + b * y 0 := by simp
    have hx1 : (a • x + b • y) 1 = a * x 1 + b * y 1 := by simp
    rw [hx0, hx1]
    have hb' : b = 1 - a := by linarith
    subst hb'
    nlinarith [mul_nonneg ha hx, mul_nonneg hb hy]
  have hsub : (baseBetaTarget e f he hef).carrier
      ⊆ {q : Plane | 0 ≤ (baseLen e f - q 0) * height e f - baseLen e f / 2 * q 1} := by
    refine convexHull_min ?_ hconv
    rintro _ ⟨k, rfl⟩
    fin_cases k <;>
      simp [baseBetaTarget, mkTri_pts, mkPt_zero, mkPt_one] <;> nlinarith
  exact fun q hq => hsub hq

/-- The value of the right functional at `J + (d, 0)`: `H·(L − f·d)/f`. -/
theorem right_value {f : ℝ} (hf : 1 < f) (d : ℝ) :
    (baseLen 1 f - (Jx f + d)) * height 1 f - baseLen 1 f / 2 * Jy f
      = height 1 f * (baseLen 1 f - f * d) / f := by
  have hf0 : f ≠ 0 := by linarith
  unfold Jx Jy sideA
  field_simp
  ring

/-- Mirrored filler: the functional at `J + (c, 0)` is `−H(f³ − 3f² + 1)/f`. -/
theorem right_mirrored {f : ℝ} (hf : 1 < f) :
    (baseLen 1 f - (Jx f + f ^ 2)) * height 1 f - baseLen 1 f / 2 * Jy f
      = -(height 1 f * (f ^ 3 - 3 * f ^ 2 + 1) / f) := by
  rw [right_value hf]; unfold baseLen Nq; ring

/-- Direct filler: the functional at `J + (b, 0)` is `−H(f³ − 3f² − f + 1)/f`. -/
theorem right_direct {f : ℝ} (hf : 1 < f) :
    (baseLen 1 f - (Jx f + (f ^ 2 - 1))) * height 1 f - baseLen 1 f / 2 * Jy f
      = -(height 1 f * (f ^ 3 - 3 * f ^ 2 - f + 1) / f) := by
  rw [right_value hf]; unfold baseLen Nq; ring

/-- A point `J + (d, 0)` with `0 < d` and `f·d > L` is outside the target. -/
theorem outside_of_gt {f : ℝ} (hf : 1 < f) {d : ℝ} (hd : baseLen 1 f < f * d) :
    mkPt (Jx f + d) (Jy f) ∉ (baseBetaTarget 1 f one_pos hf).carrier := by
  intro hmem
  have h := rightFunctional_carrier one_pos hf _ hmem
  rw [mkPt_zero, mkPt_one, right_value hf] at h
  have hH := height_pos (one_pos : (0:ℝ) < 1) hf
  have hf0 : (0:ℝ) < f := by linarith
  have : height 1 f * (baseLen 1 f - f * d) / f < 0 :=
    div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hH (by linarith)) hf0
  linarith

/-- A point `J + (d, 0)` with `0 < d` and `f·d < L` is interior to the target. -/
theorem inside_of_lt {f : ℝ} (hf : 1 < f) {d : ℝ} (hd0 : 0 < d) (hd : f * d < baseLen 1 f) :
    mkPt (Jx f + d) (Jy f) ∈ interior (baseBetaTarget 1 f one_pos hf).carrier := by
  have hH := height_pos (one_pos : (0:ℝ) < 1) hf
  have hL := baseLen_pos (one_pos : (0:ℝ) < 1) hf
  have hf0 : (0:ℝ) < f := by linarith
  have hY : 0 < Jy f := mul_pos (by linarith) (sideA_snd_pos one_pos hf)
  refine Erdos634.ChordChartPlanar.mem_interior_carrier_of_dets_pos
    (target_det_pos one_pos hf) ?_ ?_ ?_
  · -- the right side
    have hv := right_value hf d
    have hpos : 0 < height 1 f * (baseLen 1 f - f * d) / f :=
      div_pos (mul_pos hH (by linarith)) hf0
    have : det3 (Jx f + d) (Jy f) (baseLen 1 f) 0 (baseLen 1 f / 2) (height 1 f)
        = (baseLen 1 f - (Jx f + d)) * height 1 f - baseLen 1 f / 2 * Jy f := by
      unfold det3; ring
    rw [this, hv]; exact hpos
  · -- the left side
    have : det3 0 0 (Jx f + d) (Jy f) (baseLen 1 f / 2) (height 1 f) = d * height 1 f := by
      unfold det3 Jx Jy sideA
      field_simp
      ring
    rw [this]; positivity
  · -- the base
    have : det3 0 0 (baseLen 1 f) 0 (Jx f + d) (Jy f) = baseLen 1 f * Jy f := by
      unfold det3; ring
    rw [this]; positivity

/-- **Mirrored filler, outside**: if `f³ − 3f² + 1 > 0` the point `J + (c,0)` is not in the
target. -/
theorem mirrored_outside {f : ℝ} (hf : 1 < f) (h : 0 < f ^ 3 - 3 * f ^ 2 + 1) :
    mkPt (Jx f + f ^ 2) (Jy f) ∉ (baseBetaTarget 1 f one_pos hf).carrier :=
  outside_of_gt hf (by unfold baseLen Nq; nlinarith)

/-- **Mirrored filler, inside**: if `f³ − 3f² + 1 < 0` the point `J + (c,0)` is interior to the
target. -/
theorem mirrored_inside {f : ℝ} (hf : 1 < f) (h : f ^ 3 - 3 * f ^ 2 + 1 < 0) :
    mkPt (Jx f + f ^ 2) (Jy f) ∈ interior (baseBetaTarget 1 f one_pos hf).carrier :=
  inside_of_lt hf (by positivity) (by unfold baseLen Nq; nlinarith)

/-- **Direct filler, outside**: if `f³ − 3f² − f + 1 > 0` the point `J + (b,0)` is not in the
target. -/
theorem direct_outside {f : ℝ} (hf : 1 < f) (h : 0 < f ^ 3 - 3 * f ^ 2 - f + 1) :
    mkPt (Jx f + (f ^ 2 - 1)) (Jy f) ∉ (baseBetaTarget 1 f one_pos hf).carrier :=
  outside_of_gt hf (by unfold baseLen Nq; nlinarith)

/-- **Direct filler, inside**: if `f³ − 3f² − f + 1 < 0` the point `J + (b,0)` is interior to the
target. -/
theorem direct_inside {f : ℝ} (hf : 1 < f) (h : f ^ 3 - 3 * f ^ 2 - f + 1 < 0) :
    mkPt (Jx f + (f ^ 2 - 1)) (Jy f) ∈ interior (baseBetaTarget 1 f one_pos hf).carrier :=
  inside_of_lt hf (by nlinarith) (by unfold baseLen Nq; nlinarith)

/-- The mirrored polynomial at a natural number: positive iff `f ≥ 3`, never zero. -/
theorem mirrored_sign (f : ℕ) (hf : 2 ≤ f) :
    ((0:ℝ) < (f:ℝ) ^ 3 - 3 * (f:ℝ) ^ 2 + 1 ↔ 3 ≤ f) ∧
      (¬ 3 ≤ f → (f:ℝ) ^ 3 - 3 * (f:ℝ) ^ 2 + 1 < 0) := by
  refine ⟨⟨fun h => ?_, fun h => ?_⟩, fun h => ?_⟩
  · by_contra hlt
    have h2 : f = 2 := by omega
    subst h2; norm_num at h
  · have h3 : (3:ℝ) ≤ (f:ℝ) := by exact_mod_cast h
    nlinarith [mul_nonneg (sub_nonneg.mpr h3) (sq_nonneg (f:ℝ))]
  · have h2 : f = 2 := by omega
    subst h2; norm_num

/-- The direct polynomial at a natural number: positive iff `f ≥ 4`, never zero. -/
theorem direct_sign (f : ℕ) (hf : 2 ≤ f) :
    ((0:ℝ) < (f:ℝ) ^ 3 - 3 * (f:ℝ) ^ 2 - (f:ℝ) + 1 ↔ 4 ≤ f) ∧
      (¬ 4 ≤ f → (f:ℝ) ^ 3 - 3 * (f:ℝ) ^ 2 - (f:ℝ) + 1 < 0) := by
  refine ⟨⟨fun h => ?_, fun h => ?_⟩, fun h => ?_⟩
  · by_contra hlt
    have h2 : f = 2 ∨ f = 3 := by omega
    rcases h2 with h2 | h2 <;> subst h2 <;> norm_num at h
  · have h4 : (4:ℝ) ≤ (f:ℝ) := by exact_mod_cast h
    nlinarith [mul_nonneg (sub_nonneg.mpr h4) (sq_nonneg (f:ℝ))]
  · have h2 : f = 2 ∨ f = 3 := by omega
    rcases h2 with h2 | h2 <;> subst h2 <;> norm_num

/-- **`lem:topjunction`, mirrored filler**: for a natural `f ≥ 2`, the endpoint `J + (c, 0)` is
outside the target iff `f³ − 3f² + 1 > 0` iff `f ≥ 3`. -/
theorem mirrored_outside_iff (f : ℕ) (hf : 2 ≤ f) :
    let hf1 : (1:ℝ) < (f:ℝ) := by exact_mod_cast (show 1 < f by omega)
    (mkPt (Jx f + (f:ℝ) ^ 2) (Jy f) ∉ (baseBetaTarget 1 (f:ℝ) one_pos hf1).carrier
        ↔ (0:ℝ) < (f:ℝ) ^ 3 - 3 * (f:ℝ) ^ 2 + 1) ∧
      ((0:ℝ) < (f:ℝ) ^ 3 - 3 * (f:ℝ) ^ 2 + 1 ↔ 3 ≤ f) := by
  intro hf1
  have hs := mirrored_sign f hf
  refine ⟨⟨fun hout => ?_, fun h => mirrored_outside hf1 h⟩, hs.1⟩
  by_contra hneg
  have h3 : ¬ 3 ≤ f := fun h3 => hneg (hs.1.mpr h3)
  exact hout (interior_subset (mirrored_inside hf1 (hs.2 h3)))

/-- **`lem:topjunction`, direct filler**: for a natural `f ≥ 2`, the endpoint `J + (b, 0)` is
outside the target iff `f³ − 3f² − f + 1 > 0` iff `f ≥ 4`. -/
theorem direct_outside_iff (f : ℕ) (hf : 2 ≤ f) :
    let hf1 : (1:ℝ) < (f:ℝ) := by exact_mod_cast (show 1 < f by omega)
    (mkPt (Jx f + ((f:ℝ) ^ 2 - 1)) (Jy f) ∉ (baseBetaTarget 1 (f:ℝ) one_pos hf1).carrier
        ↔ (0:ℝ) < (f:ℝ) ^ 3 - 3 * (f:ℝ) ^ 2 - (f:ℝ) + 1) ∧
      ((0:ℝ) < (f:ℝ) ^ 3 - 3 * (f:ℝ) ^ 2 - (f:ℝ) + 1 ↔ 4 ≤ f) := by
  intro hf1
  have hs := direct_sign f hf
  refine ⟨⟨fun hout => ?_, fun h => direct_outside hf1 h⟩, hs.1⟩
  by_contra hneg
  have h4 : ¬ 4 ≤ f := fun h4 => hneg (hs.1.mpr h4)
  exact hout (interior_subset (direct_inside hf1 (hs.2 h4)))

end Erdos634.Draft.TopJunctionGeom
