-- Draft/FluxGRow3TargetCoords.lean — a concrete isosceles target `Tri` with angles `(α, α, π−2α)`,
-- parametrized by `(α, lam)`, for Proposition RP. Imported directly by All.lean.
--
-- Geometry (Proposition RP, Step 1): with `M` the midpoint of `BC`, the triangle `ABM` has angles
-- `α` at `B`, `π/2` at `M`, and `β` at `A`, so it is similar to the tile `T` with ratio `lam`. The
-- sides are `AB = AC = lam·c`, `BM = lam·b`, `BC = 2·lam·b`, and comparing areas gives `N = 2lam²`.
-- Here `T` is a right triangle with legs `a` (opposite `α`) and `b` (opposite `β`), hypotenuse `c`,
-- `β = π/2 − α`, `α ∉ ℚπ`.
--
-- Normalisation, as in `FluxGRow3Placement.lean`: hypotenuse `c = 1`, so `a = sin α`, `b = cos α`; the
-- base is `BC = 2lam cos α` and `AB = AC = lam`. The vertex order is `(pts 0, pts 1, pts 2) = (B, C, A)`.
--
-- The construction uses `Erdos634.SssTri.sssTri` (isosceles is the case `p = q`) and
-- `Erdos634.AngleThreshold.cos_of_sides`. `IsoTri.isoTri` is not used since its vertex order
-- (base, base, apex) differs from `(B, C, A)`. The algebraic content (height² = side² − (half-base)²)
-- is the identity behind `IsoTri.dist02`/`dist12`.
import Erdos634.SssTri
import Erdos634.AngleThreshold
import Erdos634.Draft.FluxGRow3Cancel

namespace Erdos634.Geometry.Row3

open Erdos634.Geometry Erdos634.SssTri Erdos634.AngleThreshold Real

/-! ## §1 The base and height, on the tile's `c = 1` convention

Target ABC, angles `(α, α, π − 2α)`: base `BC = 2lam cos α`, equal sides `AB = AC = lam`.  Vertex order
`(pts 0, pts 1, pts 2) = (B, C, A)`, matching `sssTri`'s `(p, q, r)` convention with
`p = dist(pts0, pts2) = AB = lam`, `q = dist(pts1, pts2) = AC = lam`, `r = dist(pts0, pts1) = BC =
2lam cos α`. -/

/-- The height `h` `sssTri` needs for the target: `h² = q² − x²` with `x = xCoord p q r`, evaluated
at `(p, q, r) = (lam, lam, 2lam cos α)`.  Closed form: `h = lam sin α`. -/
noncomputable def targetH (α lam : ℝ) : ℝ := lam * Real.sin α

/-- **The `A`-vertex `x`-coordinate, closed form.**  For the isosceles case `p = q = lam`, `xCoord`
collapses to `r / 2`, i.e. `lam cos α`. -/
theorem xCoord_iso_eval (α lam : ℝ) (hr : (2 * lam * Real.cos α : ℝ) ≠ 0) :
    xCoord lam lam (2 * lam * Real.cos α) = lam * Real.cos α := by
  have hc0 : Real.cos α ≠ 0 := by
    intro h; apply hr; rw [h]; ring
  unfold xCoord
  field_simp
  ring

theorem targetH_sq (α lam : ℝ) (hr : (2 * lam * Real.cos α : ℝ) ≠ 0) :
    targetH α lam ^ 2 = lam ^ 2 - (xCoord lam lam (2 * lam * Real.cos α)) ^ 2 := by
  have hpyth := Real.sin_sq_add_cos_sq α
  rw [xCoord_iso_eval α lam hr, targetH]
  nlinarith [hpyth]

/-- **The placement.** `(α, lam)`-generic (not tied to any dissection or tile instance): the isosceles
target `(α, α, π − 2α)` with base `BC = 2lam cos α` and equal sides `AB = AC = lam`, vertex order
`(B, C, A)`.  Requires `0 < α < π/2` and `0 < lam`. -/
noncomputable def targetIso (α lam : ℝ) (hα : 0 < α) (hα2 : α < Real.pi / 2) (hlam : 0 < lam) : Tri :=
  sssTri lam lam (2 * lam * Real.cos α) (targetH α lam)
    (mul_ne_zero (mul_ne_zero two_ne_zero hlam.ne')
      (Real.cos_pos_of_mem_Ioo ⟨by linarith, hα2⟩).ne')
    (mul_ne_zero hlam.ne'
      (Real.sin_pos_of_pos_of_lt_pi hα (by linarith [Real.pi_pos])).ne')

/-! ## §2 The three side lengths, read off the placement

Sides: `AB = AC = lamc = lam`, `BC = 2lamb = 2lam cos α` (on the `c = 1` convention). -/

theorem targetIso_dist01 (α lam : ℝ) (hα : 0 < α) (hα2 : α < Real.pi / 2) (hlam : 0 < lam) :
    dist ((targetIso α lam hα hα2 hlam).pts 0) ((targetIso α lam hα hα2 hlam).pts 1)
      = 2 * lam * Real.cos α := by
  have hc : 0 < Real.cos α := Real.cos_pos_of_mem_Ioo ⟨by linarith, hα2⟩
  exact dist01 lam lam (2 * lam * Real.cos α) (targetH α lam) (by positivity)

theorem targetIso_dist02 (α lam : ℝ) (hα : 0 < α) (hα2 : α < Real.pi / 2) (hlam : 0 < lam) :
    dist ((targetIso α lam hα hα2 hlam).pts 0) ((targetIso α lam hα hα2 hlam).pts 2) = lam := by
  have hc : 0 < Real.cos α := Real.cos_pos_of_mem_Ioo ⟨by linarith, hα2⟩
  have hr : (2 * lam * Real.cos α : ℝ) ≠ 0 := by positivity
  exact dist02 lam lam (2 * lam * Real.cos α) (targetH α lam) hlam.le (targetH_sq α lam hr)

theorem targetIso_dist12 (α lam : ℝ) (hα : 0 < α) (hα2 : α < Real.pi / 2) (hlam : 0 < lam) :
    dist ((targetIso α lam hα hα2 hlam).pts 1) ((targetIso α lam hα hα2 hlam).pts 2) = lam := by
  have hc : 0 < Real.cos α := Real.cos_pos_of_mem_Ioo ⟨by linarith, hα2⟩
  have hr : (2 * lam * Real.cos α : ℝ) ≠ 0 := by positivity
  exact dist12 lam lam (2 * lam * Real.cos α) (targetH α lam) hr hlam.le (targetH_sq α lam hr)

/-! ## §3 The angles: the shape claim of Proposition RP

Composition of `AngleThreshold.cos_of_sides` (generic law-of-cosines bridge) with the three side
lengths above, then `Real.arccos_cos` to invert `cos` on `[0, π]`, exactly as
`FluxGRow3Placement.lean` did for the tile itself. `angleAt 0` and `angleAt 1` are the two base
angles at `B`, `C` (both `α`); `angleAt 2` is the apex angle at `A` (`π − 2α`). -/

theorem targetIso_angleAt0 (α lam : ℝ) (hα : 0 < α) (hα2 : α < Real.pi / 2) (hlam : 0 < lam) :
    (targetIso α lam hα hα2 hlam).angleAt 0 = α := by
  set T := targetIso α lam hα hα2 hlam with hT
  have hc : 0 < Real.cos α := Real.cos_pos_of_mem_Ioo ⟨by linarith, hα2⟩
  have hd01 : dist (T.pts 0) (T.pts 1) = 2 * lam * Real.cos α := targetIso_dist01 α lam hα hα2 hlam
  have hd02 : dist (T.pts 0) (T.pts 2) = lam := targetIso_dist02 α lam hα hα2 hlam
  have hd12 : dist (T.pts 1) (T.pts 2) = lam := targetIso_dist12 α lam hα hα2 hlam
  have hd10 : dist (T.pts 1) (T.pts 0) = 2 * lam * Real.cos α := by rw [dist_comm]; exact hd01
  have hd20 : dist (T.pts 2) (T.pts 0) = lam := by rw [dist_comm]; exact hd02
  have hd12' : dist (T.pts 1) (T.pts 2) = lam := hd12
  have hcos : Real.cos (cornerAngle (T.pts 1) (T.pts 0) (T.pts 2)) = Real.cos α := by
    rw [cos_of_sides (T.pts 1) (T.pts 0) (T.pts 2)
      (by rw [hd10]; positivity) (by rw [hd20]; exact hlam.ne')]
    rw [hd10, hd20, hd12']
    have hden : (0:ℝ) < 2 * (2 * lam * Real.cos α) * lam := by positivity
    have hnum : (2 * lam * Real.cos α) ^ 2 + lam ^ 2 - lam ^ 2
        = Real.cos α * (2 * (2 * lam * Real.cos α) * lam) := by ring
    rw [hnum]
    field_simp
  have hmem : cornerAngle (T.pts 1) (T.pts 0) (T.pts 2) ∈ Set.Icc 0 Real.pi :=
    ⟨EuclideanGeometry.angle_nonneg _ _ _, EuclideanGeometry.angle_le_pi _ _ _⟩
  have hmem2 : α ∈ Set.Icc (0:ℝ) Real.pi := ⟨hα.le, by linarith [Real.pi_pos]⟩
  have h1 := Real.arccos_cos hmem.1 hmem.2
  have h2 := Real.arccos_cos hmem2.1 hmem2.2
  have step : cornerAngle (T.pts 1) (T.pts 0) (T.pts 2) = Real.arccos (Real.cos α) := by
    conv_lhs => rw [← h1]
    rw [hcos]
  unfold Tri.angleAt
  rw [show (0:Fin 3)+1 = 1 from rfl, show (0:Fin 3)+2 = 2 from rfl]
  rw [step, h2]

theorem targetIso_angleAt1 (α lam : ℝ) (hα : 0 < α) (hα2 : α < Real.pi / 2) (hlam : 0 < lam) :
    (targetIso α lam hα hα2 hlam).angleAt 1 = α := by
  set T := targetIso α lam hα hα2 hlam with hT
  have hc : 0 < Real.cos α := Real.cos_pos_of_mem_Ioo ⟨by linarith, hα2⟩
  have hd01 : dist (T.pts 0) (T.pts 1) = 2 * lam * Real.cos α := targetIso_dist01 α lam hα hα2 hlam
  have hd02 : dist (T.pts 0) (T.pts 2) = lam := targetIso_dist02 α lam hα hα2 hlam
  have hd12 : dist (T.pts 1) (T.pts 2) = lam := targetIso_dist12 α lam hα hα2 hlam
  have hd21 : dist (T.pts 2) (T.pts 1) = lam := by rw [dist_comm]; exact hd12
  have hd20 : dist (T.pts 2) (T.pts 0) = lam := by rw [dist_comm]; exact hd02
  have hcos : Real.cos (cornerAngle (T.pts 2) (T.pts 1) (T.pts 0)) = Real.cos α := by
    rw [cos_of_sides (T.pts 2) (T.pts 1) (T.pts 0)
      (by rw [hd21]; exact hlam.ne') (by rw [hd01]; positivity)]
    rw [hd21, hd01, hd20]
    have hnum : lam ^ 2 + (2 * lam * Real.cos α) ^ 2 - lam ^ 2
        = Real.cos α * (2 * lam * (2 * lam * Real.cos α)) := by ring
    rw [hnum]
    field_simp
  have hmem : cornerAngle (T.pts 2) (T.pts 1) (T.pts 0) ∈ Set.Icc 0 Real.pi :=
    ⟨EuclideanGeometry.angle_nonneg _ _ _, EuclideanGeometry.angle_le_pi _ _ _⟩
  have hmem2 : α ∈ Set.Icc (0:ℝ) Real.pi := ⟨hα.le, by linarith [Real.pi_pos]⟩
  have h1 := Real.arccos_cos hmem.1 hmem.2
  have h2 := Real.arccos_cos hmem2.1 hmem2.2
  have step : cornerAngle (T.pts 2) (T.pts 1) (T.pts 0) = Real.arccos (Real.cos α) := by
    conv_lhs => rw [← h1]
    rw [hcos]
  unfold Tri.angleAt
  rw [show (1:Fin 3)+1 = 2 from rfl, show (1:Fin 3)+2 = 0 from rfl]
  rw [step, h2]

theorem targetIso_angleAt2 (α lam : ℝ) (hα : 0 < α) (hα2 : α < Real.pi / 2) (hlam : 0 < lam) :
    (targetIso α lam hα hα2 hlam).angleAt 2 = Real.pi - 2 * α := by
  set T := targetIso α lam hα hα2 hlam with hT
  have hc : 0 < Real.cos α := Real.cos_pos_of_mem_Ioo ⟨by linarith, hα2⟩
  have hd01 : dist (T.pts 0) (T.pts 1) = 2 * lam * Real.cos α := targetIso_dist01 α lam hα hα2 hlam
  have hd02 : dist (T.pts 0) (T.pts 2) = lam := targetIso_dist02 α lam hα hα2 hlam
  have hd12 : dist (T.pts 1) (T.pts 2) = lam := targetIso_dist12 α lam hα hα2 hlam
  have hd02' : dist (T.pts 0) (T.pts 2) = lam := hd02
  have hd12' : dist (T.pts 1) (T.pts 2) = lam := hd12
  have hcos : Real.cos (cornerAngle (T.pts 0) (T.pts 2) (T.pts 1)) = Real.cos (Real.pi - 2 * α) := by
    rw [cos_of_sides (T.pts 0) (T.pts 2) (T.pts 1)
      (by rw [hd02']; exact hlam.ne') (by rw [hd12']; exact hlam.ne')]
    rw [hd02', hd12', hd01, Real.cos_pi_sub, Real.cos_two_mul]
    have hden : (0:ℝ) < 2 * lam * lam := by positivity
    have hnum : lam ^ 2 + lam ^ 2 - (2 * lam * Real.cos α) ^ 2
        = -(2 * Real.cos α ^ 2 - 1) * (2 * lam * lam) := by ring
    rw [hnum]
    field_simp
  have hmem : cornerAngle (T.pts 0) (T.pts 2) (T.pts 1) ∈ Set.Icc 0 Real.pi :=
    ⟨EuclideanGeometry.angle_nonneg _ _ _, EuclideanGeometry.angle_le_pi _ _ _⟩
  have hmem2 : Real.pi - 2 * α ∈ Set.Icc (0:ℝ) Real.pi := ⟨by linarith, by linarith⟩
  have h1 := Real.arccos_cos hmem.1 hmem.2
  have h2 := Real.arccos_cos hmem2.1 hmem2.2
  have step : cornerAngle (T.pts 0) (T.pts 2) (T.pts 1) = Real.arccos (Real.cos (Real.pi - 2 * α)) := by
    conv_lhs => rw [← h1]
    rw [hcos]
  unfold Tri.angleAt
  rw [show (2:Fin 3)+1 = 0 from rfl, show (2:Fin 3)+2 = 1 from rfl]
  rw [step, h2]

/-! ## §4 The angle sum — a consistency check of the three closed forms above -/

theorem targetIso_angleAt_sum (α lam : ℝ) (hα : 0 < α) (hα2 : α < Real.pi / 2) (hlam : 0 < lam) :
    (targetIso α lam hα hα2 hlam).angleAt 0 + (targetIso α lam hα hα2 hlam).angleAt 1
      + (targetIso α lam hα hα2 hlam).angleAt 2 = Real.pi := by
  rw [targetIso_angleAt0 α lam hα hα2 hlam, targetIso_angleAt1 α lam hα hα2 hlam,
    targetIso_angleAt2 α lam hα hα2 hlam]
  ring

/-! ## §5 A concrete numeric witness (sanity check, not the base-β tile)

`α = π/4`, `lam = 1`: hypotheses non-vacuous, and the target collapses to the right isosceles triangle
`(π/4, π/4, π/2)` with legs `1` and hypotenuse `√2` (`BC = 2·1·cos(π/4) = √2`, `AB = AC = 1`) — a
correct, independently checkable instance of the closed forms above.  This is a SANITY CHECK ONLY:
`α = π/4` is rational over `π` (`α/π = 1/4`), so it is NOT the `α ∉ ℚπ` regime the Corollary
needs; the general family above is parametrized to cover the actual, irrational-`α` case, which this
witness does not exercise. -/

theorem witness_hα : (0:ℝ) < Real.pi / 4 := by positivity

theorem witness_hα2 : Real.pi / 4 < Real.pi / 2 := by linarith [Real.pi_pos]

theorem witness_hlam : (0:ℝ) < 1 := one_pos

theorem witness_dist01 :
    dist ((targetIso (Real.pi/4) 1 witness_hα witness_hα2 witness_hlam).pts 0)
      ((targetIso (Real.pi/4) 1 witness_hα witness_hα2 witness_hlam).pts 1)
      = 2 * Real.cos (Real.pi/4) := by
  have h := targetIso_dist01 (Real.pi/4) 1 witness_hα witness_hα2 witness_hlam
  linarith [h]

theorem witness_angleAt2 :
    (targetIso (Real.pi/4) 1 witness_hα witness_hα2 witness_hlam).angleAt 2 = Real.pi / 2 := by
  rw [targetIso_angleAt2 (Real.pi/4) 1 witness_hα witness_hα2 witness_hlam]
  ring

end Erdos634.Geometry.Row3

#print axioms Erdos634.Geometry.Row3.targetIso_dist01
#print axioms Erdos634.Geometry.Row3.targetIso_dist02
#print axioms Erdos634.Geometry.Row3.targetIso_dist12
#print axioms Erdos634.Geometry.Row3.targetIso_angleAt0
#print axioms Erdos634.Geometry.Row3.targetIso_angleAt1
#print axioms Erdos634.Geometry.Row3.targetIso_angleAt2
#print axioms Erdos634.Geometry.Row3.targetIso_angleAt_sum
#print axioms Erdos634.Geometry.Row3.witness_dist01
#print axioms Erdos634.Geometry.Row3.witness_angleAt2
