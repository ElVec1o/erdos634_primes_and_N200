-- Draft/FluxGRow3AngleWitness.lean: a concrete `Irrational (α / π)` witness for the hypothesis `hairr` of
-- the right-tile results (`FluxGRow3Step5.witness_step5`, `FluxGRow3TargetDirs`, `FluxGRow3Weight`,
-- `FluxGRow3Placement.flux_gauss_direct_instance`, `FluxGRow3Cancel.gaussWeightA_shift`), following the
-- `α456_irr` / Niven pattern used for the tile `(4,5,6)` (`FluxRow4Witness.lean`).
--
-- The statement for isosceles targets `(α, α, π−2α)` is for a family of angles with the standing
-- requirement `α ∉ ℚπ`, `0 < α < π/2`. The Lean theorems (`targetIso_flux_gauss`, `witness_step5`,
-- `gaussWeightA_shift`, `flux_gauss_direct_instance`) are universally quantified over `α` and `lam`
-- subject only to `0 < α`, `α < π/2`, `0 < lam`, `Irrational (α/π)`, so any concrete `α` satisfying these
-- constraints is a valid witness.
--
-- Candidate angles. `α = π/4` fails `hairr` (`1/4 ∈ ℚ`). `grid_unique_witness` of `FluxGRow3.lean`
-- (`α = √2·π`) discharges `Irrational (α/π)` but is not a valid angle: `α ≈ 4.44 > π/2` fails `hα2`.
-- Angles with rational tangent (`tan α = 1/2`, `1/3`) have irrational cosines (for instance `2/√5`), so
-- Niven's cosine criterion does not apply to them directly.
--
-- `α456` (the angle at vertex 0 of the real `(4,5,6)` triangle, `cos α456 = 3/4`) already has
-- `α456_irr : ¬ ∃ r : ℚ, α456 = r * π` from Niven's theorem (`Mathlib.NumberTheory.Niven`, cosine-based),
-- proved in `FluxRow4Witness.lean`. Together with the two order facts proved below (`0 < α456`,
-- `α456 < π/2`, from `cos_α456` and `cornerAngle_mem'`) it is a witness for `hairr`, `hα` and `hα2`, and
-- instantiates `FluxGRow3Step5.witness_step5` with every hypothesis discharged.
import Erdos634.Draft.FluxGRow3Step5
import Erdos634.Draft.FluxRow4Witness

open scoped Classical

namespace Erdos634.Geometry.Row3

open Erdos634.Draft.FluxRow4Witness Erdos634.Draft.FluxPaperWitness

/-- `α456` (row 4's real `(4,5,6)`-tile angle, `cos α456 = 3/4`) is strictly positive: if it were
`0`, `cos α456` would be `cos 0 = 1`, contradicting `cos_α456 : Real.cos α456 = 3/4`. -/
theorem α456_pos : 0 < α456 := by
  have h0 : 0 ≤ α456 := (cornerAngle_mem' _ _ _).1
  rcases h0.lt_or_eq with h | h
  · exact h
  · exfalso
    have hc := cos_α456
    rw [← h, Real.cos_zero] at hc
    norm_num at hc

/-- `α456 < π/2`: `cos` is strictly decreasing on `[0, π]` (`Real.cos_lt_cos_of_nonneg_of_le_pi`);
`cos α456 = 3/4 > 0 = cos(π/2)`, so `α456 < π/2` (else `cos α456 < cos(π/2) = 0`, contradicting
`3/4 > 0`). The argument is that of `FluxRow4Witness.angle2_456` (`hle`). -/
theorem α456_lt_pi_div_two : α456 < Real.pi / 2 := by
  by_contra h
  push Not at h
  have hαπ : α456 ≤ Real.pi := (cornerAngle_mem' _ _ _).2
  rcases h.lt_or_eq with h' | h'
  · have := Real.cos_lt_cos_of_nonneg_of_le_pi (by positivity : (0:ℝ) ≤ Real.pi / 2) hαπ h'
    rw [Real.cos_pi_div_two, cos_α456] at this
    norm_num at this
  · have hc := cos_α456
    rw [← h', Real.cos_pi_div_two] at hc
    norm_num at hc

/-- `α456_irr` (`FluxRow4Witness.lean`) is stated as `¬∃ r : ℚ, α456 = r * π`; row 3's theorems want
`Irrational (α456 / π)`. The two are equivalent (`π ≠ 0`); this converts, without reproving the
underlying Niven argument. -/
theorem α456_div_pi_irr : Irrational (α456 / Real.pi) := by
  rintro ⟨r, hr⟩
  apply α456_irr
  refine ⟨r, ?_⟩
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp at hr
  linarith [hr]

/-- **The concrete row-3 witness.** `α456` satisfies every real-valued hypothesis of
`FluxGRow3Step5.witness_step5` (`0 < α456`, `α456 < π/2`, `Irrational (α456 / π)` via
`α456_irr`), so, at `lam := 1`, the theorem applies outright at every grid degree `X`: this is the
FIRST fully concrete, non-hypothetical instance of row 3's target-side flux computation with its
irrationality hypothesis genuinely discharged (not vacuous, not `α = π/4`). -/
theorem witness_step5_concrete (X : ℤ) :
    (targetIso α456 1 α456_pos α456_lt_pi_div_two one_pos).flux
        (gaussWeight α456
          ((targetIso α456 1 α456_pos α456_lt_pi_div_two one_pos).leftUnit 0).angle.toReal X)
      = (Complex.I : ℂ) ^
          (gridJ α456
            ((targetIso α456 1 α456_pos α456_lt_pi_div_two one_pos).leftUnit 0).angle.toReal
            ((targetIso α456 1 α456_pos α456_lt_pi_div_two one_pos).leftUnit 0).angle) *
        ((if gridK α456
              ((targetIso α456 1 α456_pos α456_lt_pi_div_two one_pos).leftUnit 0).angle.toReal
              ((targetIso α456 1 α456_pos α456_lt_pi_div_two one_pos).leftUnit 0).angle = X
            then (2 * (1:ℝ) * Real.cos α456 : ℂ) else 0)
          - (if gridK α456
                ((targetIso α456 1 α456_pos α456_lt_pi_div_two one_pos).leftUnit 0).angle.toReal
                ((targetIso α456 1 α456_pos α456_lt_pi_div_two one_pos).leftUnit 0).angle - 1 = X
              then ((1:ℝ) : ℂ) else 0)
          - (if gridK α456
                ((targetIso α456 1 α456_pos α456_lt_pi_div_two one_pos).leftUnit 0).angle.toReal
                ((targetIso α456 1 α456_pos α456_lt_pi_div_two one_pos).leftUnit 0).angle + 1 = X
              then ((1:ℝ) : ℂ) else 0)) :=
  witness_step5 α456 1 α456_pos α456_lt_pi_div_two one_pos α456_div_pi_irr X

end Erdos634.Geometry.Row3

#print axioms Erdos634.Geometry.Row3.α456_pos
#print axioms Erdos634.Geometry.Row3.α456_lt_pi_div_two
#print axioms Erdos634.Geometry.Row3.α456_div_pi_irr
#print axioms Erdos634.Geometry.Row3.witness_step5_concrete
