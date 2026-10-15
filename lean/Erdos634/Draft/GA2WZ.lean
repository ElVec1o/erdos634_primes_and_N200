/-
Final assembly:  `gapA2_full : GapA2`  -- hypothesis-free.
  `GA2WC.kbJ1_lab : KbJ1Lab`, `GA2WD.kcJ1_lab : KcJ1Lab`, `GA2UH.d3_lab : D3Lab` (via `GA2UI.gapA2_of_two_atoms`).
No sorry / native_decide.
-/
import Mathlib
import Erdos634.Draft.GA2WE
import Erdos634.Draft.GA2UI

namespace Erdos634.GA2WZ

theorem gapA2_full : Erdos634.CaseA.R0c15.GapA2 :=
  Erdos634.GA2UI.gapA2_of_two_atoms Erdos634.GA2WC.kbJ1_lab Erdos634.GA2WD.kcJ1_lab

end Erdos634.GA2WZ

#print axioms Erdos634.GA2WZ.gapA2_full
