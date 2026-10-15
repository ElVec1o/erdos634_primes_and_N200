-- Draft/CaseALemmaHWitness.lean — witnesses for Draft/CaseALemmaH.lean (Case A, Lemma H).
-- `count_eq_witness`: `count_eq` applied to the real `CongruentDissection 2` `dissection'`
-- (FluxGRow3WitnessBridge; α = α456, which is NOT in ℚπ — `count_eq` needs no rationality), every
-- hypothesis discharged.  `hcore_witness`: `HCore` holds at a genuine rational angle (π/4).
-- The joint witness for the full hypothesis bundle is in CaseALemmaHPiFour.lean.
-- Imported directly by `All`.
import Erdos634.Draft.CaseALemmaH
import Erdos634.Draft.FluxGRow3RPAnyLabelWitness

namespace Erdos634.Draft.CaseALemmaHWitness

open Erdos634.Geometry Erdos634.CertCoord Erdos634.AngleThreshold
open Erdos634.Draft.FluxGRow3AngleWitnessDissection Erdos634.Draft.FluxGRow3WitnessBridge
open Erdos634.Draft.FluxGRow3SharedGrid Erdos634.Draft.FluxGRow3Step3N2Final
open Erdos634.Draft.FluxRow4Witness Erdos634.Geometry.Row3 Erdos634.Draft.FluxGRow3RPWitness
open Erdos634.Geometry.CaseA.LemmaH

theorem count_eq_witness :
    ∃ r x y : ℕ, ((2 : ℕ) : ℝ) = 2 * ((r : ℝ) + x * Real.sin α456 + y * Real.cos α456) ^ 2 :=
  count_eq dissection' α456_pos α456_lt_pi_div_two
    (p := 0) (q := 2) (by decide) model'_angleAt0 tile0'_angleAt2
    (i := 0) (j := 1) (by decide) target_angleAt0 target_angleAt1

theorem hcore_witness : HCore (Real.pi / 4) := core_pi_div_four

/-- Control: the prime bound in `HCore` is needed — `p = 2` is attained (r = 1, x = y = 0). -/
theorem control_p2 : 2 * (((1 : ℕ) : ℝ) + (0 : ℕ) * Real.sin (Real.pi / 4)
    + (0 : ℕ) * Real.cos (Real.pi / 4)) ^ 2 = ((2 : ℕ) : ℝ) := by norm_num

end Erdos634.Draft.CaseALemmaHWitness

#print axioms Erdos634.Draft.CaseALemmaHWitness.count_eq_witness
#print axioms Erdos634.Draft.CaseALemmaHWitness.hcore_witness
