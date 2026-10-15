/- Part of a split of the AllN2 checks into smaller modules (AllN2Check6). No sorry, no native_decide. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

theorem not_C_87_old : ¬ C 87 := by decide +kernel
theorem not_C_159_old : ¬ C 159 := by decide +kernel
theorem not_C'_21 : ¬ C' 21 := by decide +kernel
theorem not_C'_33 : ¬ C' 33 := by decide +kernel
theorem not_C'_70 : ¬ C' 70 := by decide +kernel
theorem not_C'_15 : ¬ C' 15 := by decide +kernel
theorem not_C'_30 : ¬ C' 30 := by decide +kernel
theorem not_C'_255 : ¬ C' 255 := by decide +kernel
theorem not_C'_105 : ¬ C' 105 := by decide +kernel

end Erdos634.Draft.AllN2

#print axioms Erdos634.Draft.AllN2.not_C'_255
