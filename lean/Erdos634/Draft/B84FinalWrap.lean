import Erdos634.B84Final

namespace Erdos634.Draft.B84FinalWrap
open Erdos634.B84
open Erdos634.Geometry Erdos634.BADL2
open Erdos634.Draft.FDBBaseBetaE1 (HasSides)

variable {N : ℕ}

/-- The N=84 witness: exists D satisfying Hyp 1 2 24 42. -/
theorem wrap_witness84 : ∃ D : CongruentDissection 84, Hyp 1 2 24 42 D :=
  witness84

/-- Applying theoremA to the 84 witness gives w: 24 = 4w, 42 = 7w, 3 ∣ w. -/
theorem wrap_theoremA_at_84 : ∃ D : CongruentDissection 84, Hyp 1 2 24 42 D ∧
    ∃ w : ℤ, (24 : ℝ) = (2 : ℝ) ^ 2 * w ∧ (42 : ℝ) = (2 * (2 : ℝ) ^ 2 - 1 ^ 2) * w ∧
      ((2 : ℤ) ^ 2 - 1 ^ 2) ∣ w :=
  theoremA_at_84

/-- Counterexample: Hyp 1 3 X Y D is impossible when D.model has sides 2 3 4. -/
theorem wrap_control_13 (D : CongruentDissection N) (hm : HasSides D.model 2 3 4)
    (X Y : ℝ) : ¬ Hyp 1 3 X Y D :=
  control_13 D hm X Y

/-- The control applies to the actual 84-tile witness. -/
theorem wrap_control_13_at_84 : ∃ D : CongruentDissection 84, HasSides D.model 2 3 4 ∧
    ∀ X Y : ℝ, ¬ Hyp 1 3 X Y D :=
  control_13_at_84

example : True := trivial

#print axioms wrap_theoremA_at_84

end Erdos634.Draft.B84FinalWrap
