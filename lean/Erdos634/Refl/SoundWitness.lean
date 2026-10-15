import Erdos634.Refl.DataA
import Erdos634.Refl.SoundStage13
/-! Non-vacuity of the instance-level hypotheses of `checkNode_sound` on the real N=15 instance of `DataA`. -/
open Refl
theorem wA_ok : inst.ok = true := by decide +kernel
theorem wA_base : inst.baseY = true := by decide +kernel
theorem wA_check : inst.checkAll 100 tree = true := by decide +kernel
#print axioms wA_ok
#print axioms wA_base
#print axioms wA_check
