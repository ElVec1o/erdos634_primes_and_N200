-- Draft/FluxGRow3Placement.lean — a concrete placed right `Tri` with angles `(α, π/2−α, π/2)`, and an
-- evaluated instance of `Tri.flux_gauss_direct`. Imported directly by All.lean.
--
-- The placement is a composition of two generic constructions:
--   1. `Erdos634.SssTri.sssTri p q r h hr hh : Tri` places a triangle from its three side lengths, with
--      base `[0,0] → [r,0]` and apex at `(xCoord p q r, h)`.
--   2. `Erdos634.AngleThreshold.cos_of_sides p q r hp hr` gives `cos (cornerAngle p q r)` by the law of
--      cosines; with `Real.arccos_cos` this extracts the angles.
-- No rotation or `Dir`-level construction is needed. `Tri` itself is `structure Tri where pts : Fin 3 →
-- Plane; indep : AffineIndependent ℝ pts`; the side-data constructors available are `sssTri` (SSS) and
-- `IsoTri.isoTri` (isosceles).
--
-- Main declarations: `right_tile_sides` and `flux_gauss_direct_instance`.
import Erdos634.SssTri
import Erdos634.AngleThreshold
import Erdos634.Draft.FluxGRow3Cancel

namespace Erdos634.Geometry.Row3

open Erdos634.Geometry Erdos634.SssTri Erdos634.AngleThreshold Real

/-! ## §1 The three side lengths and the height, at hypotenuse `c = 1`

Right tile `(α, π/2 − α, π/2)` at vertices `(0, 1, 2) = (A, B, C)`: `∠A = α`, `∠B = π/2 − α`,
`∠C = π/2`.  By the law of sines with hypotenuse `AB = 1`: `BC = sin α` (opposite `α`),
`CA = cos α` (opposite `π/2 − α`).  `sssTri`'s three side parameters `(p, q, r)` are literally
`(BC, CA, AB) = (sin α, cos α, 1)`. -/

/-- The height `h` `sssTri` needs: `h² = q² − x²` with `x = xCoord p q r`, evaluated at
`(p, q, r) = (sin α, cos α, 1)`.  Closed form: `h = cos α · sin α` (both factors positive on
`(0, π/2)`, so this is also `> 0`, i.e. the placement is *positively oriented*, matching
`Tri.flux_gauss_direct`'s `0 < T.det` "direct copy" hypothesis). -/
noncomputable def rightH (α : ℝ) : ℝ := Real.cos α * Real.sin α

theorem xCoord_eval (α : ℝ) : xCoord (Real.sin α) (Real.cos α) 1 = Real.cos α ^ 2 := by
  have hpyth := Real.sin_sq_add_cos_sq α
  unfold xCoord
  field_simp
  nlinarith

theorem rightH_sq (α : ℝ) :
    rightH α ^ 2 = Real.cos α ^ 2 - (xCoord (Real.sin α) (Real.cos α) 1) ^ 2 := by
  have hpyth := Real.sin_sq_add_cos_sq α
  have h : Real.sin α ^ 2 = 1 - Real.cos α ^ 2 := by linarith
  rw [xCoord_eval, rightH, mul_pow, h]
  ring

/-- **The placement.**  `α`-generic (not tied to any dissection or model tile): the right tile
`(α, π/2 − α, π/2)` with hypotenuse `1`, base `A → B` on the `x`-axis, apex `C` above it. -/
noncomputable def rightTilePlacement (α : ℝ) (hα : 0 < α) (hα2 : α < Real.pi / 2) : Tri :=
  sssTri (Real.sin α) (Real.cos α) 1 (rightH α) one_ne_zero
    (by
      have hs : 0 < Real.sin α := Real.sin_pos_of_pos_of_lt_pi hα (by linarith [Real.pi_pos])
      have hc : 0 < Real.cos α := Real.cos_pos_of_mem_Ioo ⟨by linarith, hα2⟩
      exact ne_of_gt (mul_pos hc hs))

/-! ## §2 The three side lengths, read off the placement -/

theorem rightTilePlacement_dist01 (α : ℝ) (hα : 0 < α) (hα2 : α < Real.pi / 2) :
    dist ((rightTilePlacement α hα hα2).pts 0) ((rightTilePlacement α hα hα2).pts 1) = 1 :=
  dist01 (Real.sin α) (Real.cos α) 1 (rightH α) zero_le_one

theorem rightTilePlacement_dist02 (α : ℝ) (hα : 0 < α) (hα2 : α < Real.pi / 2) :
    dist ((rightTilePlacement α hα hα2).pts 0) ((rightTilePlacement α hα hα2).pts 2)
      = Real.cos α := by
  have hc : 0 ≤ Real.cos α := (Real.cos_pos_of_mem_Ioo ⟨by linarith, hα2⟩).le
  exact dist02 (Real.sin α) (Real.cos α) 1 (rightH α) hc (rightH_sq α)

theorem rightTilePlacement_dist12 (α : ℝ) (hα : 0 < α) (hα2 : α < Real.pi / 2) :
    dist ((rightTilePlacement α hα hα2).pts 1) ((rightTilePlacement α hα hα2).pts 2)
      = Real.sin α := by
  have hs : 0 ≤ Real.sin α := (Real.sin_pos_of_pos_of_lt_pi hα (by linarith [Real.pi_pos])).le
  exact dist12 (Real.sin α) (Real.cos α) 1 (rightH α) one_ne_zero hs (rightH_sq α)

/-! ## §3 The angles, both of `Tri.flux_gauss_direct`'s hypotheses

Composition of `AngleThreshold.cos_of_sides` (generic law-of-cosines bridge, cited not re-derived)
with the three side lengths above, then `Real.arccos_cos` to invert `cos` on `[0, π]` (the range
`cornerAngle`, hence `Tri.angleAt`, always lies in — `EuclideanGeometry.angle_nonneg`,
`EuclideanGeometry.angle_le_pi`). -/

theorem rightTilePlacement_angleAt2 (α : ℝ) (hα : 0 < α) (hα2 : α < Real.pi / 2) :
    (rightTilePlacement α hα hα2).angleAt 2 = Real.pi / 2 := by
  set T := rightTilePlacement α hα hα2 with hT
  have hcpos : 0 < Real.cos α := Real.cos_pos_of_mem_Ioo ⟨by linarith, hα2⟩
  have hspos : 0 < Real.sin α := Real.sin_pos_of_pos_of_lt_pi hα (by linarith [Real.pi_pos])
  have hd02 : dist (T.pts 0) (T.pts 2) = Real.cos α := rightTilePlacement_dist02 α hα hα2
  have hd12 : dist (T.pts 1) (T.pts 2) = Real.sin α := rightTilePlacement_dist12 α hα hα2
  have hd01 : dist (T.pts 0) (T.pts 1) = 1 := rightTilePlacement_dist01 α hα hα2
  have hc : Real.cos (cornerAngle (T.pts 0) (T.pts 2) (T.pts 1)) = 0 := by
    rw [cos_of_sides (T.pts 0) (T.pts 2) (T.pts 1)
      (by rw [hd02]; exact hcpos.ne') (by rw [hd12]; exact hspos.ne')]
    rw [hd02, hd12, hd01]
    have h := Real.sin_sq_add_cos_sq α
    have hden : (0:ℝ) < 2 * Real.cos α * Real.sin α := by positivity
    have hnum : Real.cos α ^ 2 + Real.sin α ^ 2 - 1 ^ 2 = 0 := by nlinarith
    rw [hnum, zero_div]
  have hmem : cornerAngle (T.pts 0) (T.pts 2) (T.pts 1) ∈ Set.Icc 0 Real.pi :=
    ⟨EuclideanGeometry.angle_nonneg _ _ _, EuclideanGeometry.angle_le_pi _ _ _⟩
  have hres := Real.arccos_cos hmem.1 hmem.2
  rw [hc, Real.arccos_zero] at hres
  unfold Tri.angleAt
  rw [show (2:Fin 3)+1 = 0 from rfl, show (2:Fin 3)+2 = 1 from rfl]
  exact hres.symm

theorem rightTilePlacement_angleAt1 (α : ℝ) (hα : 0 < α) (hα2 : α < Real.pi / 2) :
    (rightTilePlacement α hα hα2).angleAt 1 = Real.pi / 2 - α := by
  set T := rightTilePlacement α hα hα2 with hT
  have hspos : 0 < Real.sin α := Real.sin_pos_of_pos_of_lt_pi hα (by linarith [Real.pi_pos])
  have hd12 : dist (T.pts 1) (T.pts 2) = Real.sin α := rightTilePlacement_dist12 α hα hα2
  have hd01 : dist (T.pts 0) (T.pts 1) = 1 := rightTilePlacement_dist01 α hα hα2
  have hd02 : dist (T.pts 0) (T.pts 2) = Real.cos α := rightTilePlacement_dist02 α hα hα2
  have hd21 : dist (T.pts 2) (T.pts 1) = Real.sin α := by rw [dist_comm]; exact hd12
  have hd20 : dist (T.pts 2) (T.pts 0) = Real.cos α := by rw [dist_comm]; exact hd02
  have hc : Real.cos (cornerAngle (T.pts 2) (T.pts 1) (T.pts 0)) = Real.sin α := by
    rw [cos_of_sides (T.pts 2) (T.pts 1) (T.pts 0)
      (by rw [hd21]; exact hspos.ne') (by rw [hd01]; exact one_ne_zero)]
    rw [hd21, hd01, hd20]
    have h := Real.sin_sq_add_cos_sq α
    have hnum : Real.sin α ^ 2 + 1 ^ 2 - Real.cos α ^ 2 = Real.sin α * (2 * Real.sin α * 1) := by
      nlinarith
    rw [hnum]
    have hne : (2:ℝ) * Real.sin α * 1 ≠ 0 := by positivity
    field_simp
  have hmem : cornerAngle (T.pts 2) (T.pts 1) (T.pts 0) ∈ Set.Icc 0 Real.pi :=
    ⟨EuclideanGeometry.angle_nonneg _ _ _, EuclideanGeometry.angle_le_pi _ _ _⟩
  have hmem2 : Real.pi / 2 - α ∈ Set.Icc (0:ℝ) Real.pi := ⟨by linarith, by linarith [Real.pi_pos]⟩
  have h1 := Real.arccos_cos hmem.1 hmem.2
  have h2 := Real.arccos_cos hmem2.1 hmem2.2
  rw [Real.cos_pi_div_two_sub] at h2
  have step1 : cornerAngle (T.pts 2) (T.pts 1) (T.pts 0) = Real.arccos (Real.sin α) := by
    conv_lhs => rw [← h1]
    rw [hc]
  unfold Tri.angleAt
  rw [show (1:Fin 3)+1 = 2 from rfl, show (1:Fin 3)+2 = 0 from rfl]
  rw [step1, h2]

/-! ## §4 The determinant sign — direct chirality -/

theorem rightTilePlacement_det (α : ℝ) (hα : 0 < α) (hα2 : α < Real.pi / 2) :
    (rightTilePlacement α hα hα2).det = Real.cos α * Real.sin α := by
  set T := rightTilePlacement α hα hα2 with hT
  have hp0 := (coord0 (Real.sin α) (Real.cos α) 1 (rightH α)).1
  have hp1 := (coord0 (Real.sin α) (Real.cos α) 1 (rightH α)).2.1
  have hpx2 := (coord0 (Real.sin α) (Real.cos α) 1 (rightH α)).2.2
  have hq0 := (coord1 (Real.sin α) (Real.cos α) 1 (rightH α)).1
  have hq1 := (coord1 (Real.sin α) (Real.cos α) 1 (rightH α)).2.1
  have hq2 := (coord1 (Real.sin α) (Real.cos α) 1 (rightH α)).2.2
  unfold Tri.det
  show (T.pts 1 - T.pts 0) 0 * (T.pts 2 - T.pts 0) 1 - (T.pts 1 - T.pts 0) 1 * (T.pts 2 - T.pts 0) 0
    = _
  simp only [PiLp.sub_apply]
  have e0 : T.pts 0 0 = 0 := hp0
  have e1 : T.pts 1 0 = 1 := hp1
  have e2 : T.pts 0 1 = 0 := hq0
  have e3 : T.pts 1 1 = 0 := hq1
  have e4 : T.pts 2 1 = rightH α := hq2
  rw [e0, e1, e2, e3, e4]
  unfold rightH; ring

theorem rightTilePlacement_det_pos (α : ℝ) (hα : 0 < α) (hα2 : α < Real.pi / 2) :
    0 < (rightTilePlacement α hα hα2).det := by
  rw [rightTilePlacement_det]
  exact mul_pos (Real.cos_pos_of_mem_Ioo ⟨by linarith, hα2⟩)
    (Real.sin_pos_of_pos_of_lt_pi hα (by linarith [Real.pi_pos]))

/-! ## §5 A grid witness, generically, for ANY tile

`IsGridA` only asks for SOME real representative `θ₀` of the direction's `Real.Angle` class with
`k = j = 0`; every `Real.Angle` has one (surjectivity of `ℝ → Real.Angle`).  This is not special to
`rightTilePlacement`: it is the trivial grid witness available for any direction whatsoever, and is
exactly what is needed to instantiate `Tri.flux_gauss_direct`'s `hgrid` hypothesis with a *witness*
rather than an assumption. -/

theorem exists_gridWitness (α : ℝ) (θ : Real.Angle) : ∃ θ₀ : ℝ, IsGridA α θ₀ θ := by
  induction θ using Real.Angle.induction_on with
  | h θ₀ => exact ⟨θ₀, 0, 0, by push_cast; ring_nf⟩

/-! ## §6 The witnessed instance

**The first evaluated (not merely hypothetical) instance of `Tri.flux_gauss_direct`.**  Fix any
`0 < α < π/2` with `α / π` irrational (`Irrational (α / π)` — needed by `Tri.flux_gauss_direct`
itself, via `gaussWeightA_shift`; it is NOT extra baggage from this file). Then
`rightTilePlacement α hα hα2` is a genuine, fully-coordinate `Tri` discharging EVERY hypothesis of
`Tri.flux_gauss_direct` — `0 < T.det` (§4), `T.angleAt 1 = π/2 − α` and `T.angleAt 2 = π/2` (§3), and
a grid witness for `(T.leftUnit 0).angle` (§5, trivially available for this or any direction) — so
the theorem *applies*, producing a concrete equation for `T.flux (gaussWeight α θ₀ X)` at every
integer `X`. This is the "actual evaluated instance, not a hypothetical", asked for in item 3: no
step from here to `Tri.flux_gauss_direct`'s conclusion is left open. -/
theorem flux_gauss_direct_instance (α : ℝ) (hα : 0 < α) (hα2 : α < Real.pi / 2)
    (hirr : Irrational (α / Real.pi)) (X : ℤ) :
    ∃ θ₀ : ℝ,
      (rightTilePlacement α hα hα2).flux (gaussWeight α θ₀ X)
        = (Complex.I : ℂ) ^ (gridJ α θ₀ ((rightTilePlacement α hα hα2).leftUnit 0).angle) *
            ((if gridK α θ₀ ((rightTilePlacement α hα hα2).leftUnit 0).angle = X
                then ((rightTilePlacement α hα hα2).oppLen 2 : ℂ) else 0)
              - (if gridK α θ₀ ((rightTilePlacement α hα hα2).leftUnit 0).angle + 1 = X then
                  (((rightTilePlacement α hα hα2).oppLen 1 : ℂ)
                    - (rightTilePlacement α hα hα2).oppLen 0 * Complex.I) else 0)) := by
  set T := rightTilePlacement α hα hα2 with hTdef
  obtain ⟨θ₀, hgrid⟩ := exists_gridWitness α (T.leftUnit 0).angle
  exact ⟨θ₀,
    Tri.flux_gauss_direct T hirr (rightTilePlacement_det_pos α hα hα2)
      (rightTilePlacement_angleAt1 α hα hα2) (rightTilePlacement_angleAt2 α hα hα2) hgrid X⟩

end Erdos634.Geometry.Row3

#print axioms Erdos634.Geometry.Row3.rightTilePlacement_angleAt2
#print axioms Erdos634.Geometry.Row3.rightTilePlacement_angleAt1
#print axioms Erdos634.Geometry.Row3.rightTilePlacement_det_pos
#print axioms Erdos634.Geometry.Row3.exists_gridWitness
#print axioms Erdos634.Geometry.Row3.flux_gauss_direct_instance
