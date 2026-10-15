-- Draft/FluxGRow3RPAnyLabelWitness.lean — joint witness for the any-label RP wrappers
-- (FluxGRow3RPAnyLabel.lean) on the same real `CongruentDissection 2` `dissection'` used by
-- FluxGRow3RPWitness.lean (α = α456). Imported directly by All.lean.
-- No parameter pair (e, f) is evaluated here.
import Erdos634.Draft.FluxGRow3RPAnyLabel
import Erdos634.Draft.FluxGRow3RPWitness

open scoped Classical

namespace Erdos634.Draft.FluxGRow3RPAnyLabelWitness

open Erdos634.Geometry Erdos634.CertCoord Erdos634.AngleThreshold
open Erdos634.Draft.FluxGRow3AngleWitnessDissection Erdos634.Draft.FluxGRow3WitnessBridge
open Erdos634.Draft.FluxGRow3SharedGrid Erdos634.Draft.FluxGRow3Step3N2Final
open Erdos634.Draft.FluxRow4Witness Erdos634.Geometry.Row3 Erdos634.Draft.FluxGRow3RPWitness

theorem row3_RP_even_any_label_witness : Even 2 :=
  RP.row3_RP_even_any_label dissection' α456_pos α456_lt_pi_div_two α456_div_pi_irr
    (p := 0) (q := 2) (by decide) model'_angleAt0 tile0'_angleAt2 (Or.inl rfl)
    (i := 0) (j := 1) (by decide) target_angleAt0 target_angleAt1

theorem row3_RP_area_any_label_witness :
    ((2 : ℕ) : ℝ) = 2 * (dissection'.target.oppLen 1 / dissection'.model.oppLen 2) ^ 2 :=
  RP.row3_RP_area_any_label dissection' α456_pos α456_lt_pi_div_two
    (p := 0) (q := 2) (by decide) model'_angleAt0 tile0'_angleAt2 (Or.inl rfl)
    (i := 0) (j := 1) (by decide) target_angleAt0 target_angleAt1

end Erdos634.Draft.FluxGRow3RPAnyLabelWitness

#print axioms Erdos634.Draft.FluxGRow3RPAnyLabelWitness.row3_RP_even_any_label_witness
#print axioms Erdos634.Draft.FluxGRow3RPAnyLabelWitness.row3_RP_area_any_label_witness
