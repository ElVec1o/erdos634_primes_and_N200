-- Draft/FluxGRow3DirAngle.lean — computing `Dir.angle` from coordinates: given `v.1 = r * cos θ`,
-- `v.2 = r * sin θ` for `r > 0`, the direction's `Dir.angle` equals `(θ : Real.Angle)`
-- (`dir_angle_of_coords`, and the raw-vector form `arg_toC_of_coords`). Imported directly by All.lean.
--
-- Background: `Dir.angle d = (Complex.arg (toC d.1) : Real.Angle)` (`FluxTurn.lean`), and
-- `Tri.leftUnit_angle` computes the angle of a normalised `Dir` as the `Complex.arg` of the raw vector,
-- using `Complex.arg_real_mul` for a positive scalar. The proof here uses Mathlib's
-- `arg_mul_cos_add_sin_mul_I_coe_angle` together with `Real.Angle.cos_coe` and `Real.Angle.sin_coe`.
--
-- Existing `Dir.angle` facts (`Tri.leftUnit_angle`, `Tri.leftUnit_turn_of_pos/neg`, `Dir.angle_neg`)
-- are relative statements about the turning of one triangle; this lemma gives the absolute angle of a
-- direction from raw coordinates.
--
-- The numeric check in section 3 uses the side lengths `3` and `4` of the `3-√7-4` right triangle, not
-- an `(e, f)` tile-parameter pair.
import Erdos634.Draft.FluxTurn
import Erdos634.Draft.FluxGRow3WitnessBridge
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle

namespace Erdos634.Draft.FluxGRow3DirAngle

open Erdos634.Geometry Complex

/-! ## §1 The coordinate-to-`ℂ` bridge

`toC v` reads off as `r * (cos θ + sin θ * I)` exactly when `v`'s own coordinates are `r cos θ`,
`r sin θ`. This is pure algebra (`toC_apply` unfolds to the two coordinate projections), no new
geometric content — it is the precise "bridge concrete numeric triangle coordinates to the abstract
grid-membership machinery" step P110 asked for, made explicit as its own lemma so the trigonometric
step (§2) never has to touch `Plane`/`toC` directly. -/

theorem toC_eq_of_coords (v : Plane) (r θ : ℝ) (hx : v 0 = r * Real.cos θ)
    (hy : v 1 = r * Real.sin θ) :
    toC v = (r : ℂ) * (Real.cos θ + Real.sin θ * I) := by
  rw [toC_apply, hx, hy]
  push_cast
  ring

/-! ## §2 The trigonometric core: `Complex.arg` of `(r cos θ, r sin θ)` is `θ` in `Real.Angle`

This is exactly Mathlib's `arg_mul_cos_add_sin_mul_I_coe_angle`, ported from `Real.Angle.cos/sin`
of a `Real.Angle` argument to `Real.cos/Real.sin` of a raw `ℝ` argument via `Real.Angle.cos_coe`/
`sin_coe` — the "cos/sin-to-`Real.Angle` conversion helper" P110 confirmed does not exist anywhere
in the corpus for the raw-angle form actually needed here (Mathlib's own lemma is stated one level
up, at `Real.Angle`-valued `θ`, not `ℝ`-valued `θ`). -/

theorem arg_coords (r θ : ℝ) (hr : 0 < r) :
    (Complex.arg ((r : ℂ) * (Real.cos θ + Real.sin θ * I)) : Real.Angle) = (θ : Real.Angle) := by
  have h := arg_mul_cos_add_sin_mul_I_coe_angle hr (θ : Real.Angle)
  rwa [Real.Angle.cos_coe, Real.Angle.sin_coe] at h

/-! ## §3 The assembled helper, at the `Plane`/`toC` level (raw vector, no `Dir` needed yet)

Stated for a raw nonzero `v` rather than a pre-built `Dir`, matching how `Tri.leftUnit_angle`
(`FluxTurn.lean:76-81`) itself operates on the raw `leftDir` before any `Dir` is built — so this
composes directly with that lemma without an extra normalisation step. -/

theorem arg_toC_of_coords (v : Plane) (r θ : ℝ) (hr : 0 < r) (hx : v 0 = r * Real.cos θ)
    (hy : v 1 = r * Real.sin θ) :
    (Complex.arg (toC v) : Real.Angle) = (θ : Real.Angle) := by
  rw [toC_eq_of_coords v r θ hx hy]
  exact arg_coords r θ hr

/-- **The `v ≠ 0` witness is not a separate hypothesis to carry**: `r > 0` alone forces it, since
`toC` is injective and `toC v = r ≠ 0` copies of a nonzero complex number. Recorded so callers never
need to reprove nonvanishing by hand from the coordinate data. -/
theorem ne_zero_of_coords (v : Plane) (r θ : ℝ) (hr : 0 < r) (hx : v 0 = r * Real.cos θ)
    (hy : v 1 = r * Real.sin θ) : v ≠ 0 := by
  intro h
  have heq : toC v = 0 := by rw [h]; simp
  rw [toC_eq_of_coords v r θ hx hy] at heq
  have h1 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have h2 : (Real.cos θ + Real.sin θ * I : ℂ) ≠ 0 := by
    intro hc
    have hre := congrArg Complex.re hc
    have him := congrArg Complex.im hc
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, Complex.zero_re, Complex.add_im, Complex.mul_im, Complex.zero_im] at hre him
    nlinarith [Real.sin_sq_add_cos_sq θ]
  exact (mul_ne_zero h1 h2) heq

/-! ## §4 The `Dir`-level statement

Given a `Dir` `d` whose underlying vector's coordinates are `(r cos θ, r sin θ)` for some `r > 0`
(the vector need not itself be the unit vector `(cos θ, sin θ)` — `Dir.angle` is scale-invariant,
exactly as `Tri.leftUnit_angle` exploits), `d.angle = (θ : Real.Angle)`. This is the exact shape
P110 asked for: "given a 2D vector `v` ... conclude the normalized direction's `angle` equals
`(θ : Real.Angle)`" — `d.1` plays the role of `v`, and `d.2 : ‖d.1‖ = 1` is never used in the proof
(only `r > 0` is), matching the scale-invariance remark above. -/

theorem dir_angle_of_coords (d : Dir) (r θ : ℝ) (hr : 0 < r) (hx : d.1 0 = r * Real.cos θ)
    (hy : d.1 1 = r * Real.sin θ) : d.angle = (θ : Real.Angle) := by
  unfold Dir.angle
  exact arg_toC_of_coords d.1 r θ hr hx hy

end Erdos634.Draft.FluxGRow3DirAngle

/-! ## §5 Sanity check: `tile0'`'s actual `B − A` direction (P110)

Not a new consumer, not integrated anywhere — a standalone non-vacuous witness that §3/§4 actually
fire on the concrete numeric data P110 quoted by hand ("`tile0''s hypotenuse direction (B−A, length
4, cos=−3/4, sin=−√7/4)`"), imported read-only from `FluxGRow3WitnessBridge.lean` (`tile0'_pts`,
`sq7`/`sq7_pos`/`sq7_sq`), itself already compiled and integrated (P106-109). This section is
EXTRA to the requested helper, not a dependency of §1-§4, and adds no new axiom. -/
section SanityCheck

open Erdos634.Geometry Complex Erdos634.CertCoord
open Erdos634.Draft.FluxGRow3AngleWitnessDissection Erdos634.Draft.FluxGRow3WitnessBridge

/-- The raw (unnormalised) `B − A` vector of `tile0'` has coordinates `(-3, -√7)`. -/
theorem tile0'_BA_coords :
    (tile0'.pts 0 - tile0'.pts 1) 0 = -3 ∧ (tile0'.pts 0 - tile0'.pts 1) 1 = -sq7 := by
  rw [tile0'_pts]
  constructor <;> simp [PiLp.sub_apply, mkPt_zero, mkPt_one]

/-- The angle `θ := -arccos(-3/4)` reproduces `tile0'`'s hypotenuse direction exactly: applying
`arg_toC_of_coords` (§3) to the raw vector `B − A` (`r = 4`, matching its length `4` from
`FluxGRow3WitnessBridge.model'_dBA`) with this `θ` computes `Complex.arg (toC (B - A))`
unconditionally — the helper is not vacuous, it fires on genuine non-contradictory numeric data. -/
theorem tile0'_BA_angle :
    (Complex.arg (toC (tile0'.pts 0 - tile0'.pts 1)) : Real.Angle)
      = ((-Real.arccos (-3/4 : ℝ) : ℝ) : Real.Angle) := by
  obtain ⟨hx0, hy0⟩ := tile0'_BA_coords
  have hs7 := sq7_pos
  have h7 := sq7_sq
  have hcos : Real.cos (-Real.arccos (-3/4 : ℝ)) = -3/4 := by
    rw [Real.cos_neg, Real.cos_arccos (by norm_num) (by norm_num)]
  have hsin : Real.sin (-Real.arccos (-3/4 : ℝ)) = -sq7 / 4 := by
    rw [Real.sin_neg, Real.sin_arccos]
    have heq : (1 : ℝ) - (-3/4)^2 = (sq7/4)^2 := by
      have : (sq7/4)^2 = sq7^2 / 16 := by ring
      rw [this, h7]; norm_num
    rw [heq, Real.sqrt_sq (by positivity), neg_div]
  refine Erdos634.Draft.FluxGRow3DirAngle.arg_toC_of_coords _ 4 _ (by norm_num) ?_ ?_
  · rw [hx0, hcos]; ring
  · rw [hy0, hsin]; ring

end SanityCheck

#print axioms tile0'_BA_coords
#print axioms tile0'_BA_angle

#print axioms Erdos634.Draft.FluxGRow3DirAngle.toC_eq_of_coords
#print axioms Erdos634.Draft.FluxGRow3DirAngle.arg_coords
#print axioms Erdos634.Draft.FluxGRow3DirAngle.arg_toC_of_coords
#print axioms Erdos634.Draft.FluxGRow3DirAngle.ne_zero_of_coords
#print axioms Erdos634.Draft.FluxGRow3DirAngle.dir_angle_of_coords
