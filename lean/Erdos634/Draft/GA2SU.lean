/-
Assembly: `gapA2_of_residual_k : PartD3 -> PartKb3Open -> PartKc3Open -> GapA2`.

GapA2 (N = 15, Case A) follows from GA2QG.gapA2_of_parts3 with
  PartN3060 : GA2RF.partN3060          (n = 30, 60)
  PartKa    : GA2SH.partKa              (i = 2, k >= 2, j >= 1)
  PartKb3   : GA2SN.partKb3_of_open     (i = 0, k >= 2, entry T divisible by 3: j >= 2 proved here; j = 1 left as `PartKb3Open`)
  PartKc3   : GA2ST.partKc3_of_open     (i = 1, k >= 2, entry T divisible by 3: T odd (any j) and j >= 2 proved here; j = 1 with T even left as `PartKc3Open`)
The three remaining hypotheses are exactly: `PartD3`, `PartKb3Open`, `PartKc3Open`.
No sorry / native_decide.
-/
import Mathlib
import Erdos634.Draft.GA2RF
import Erdos634.Draft.GA2SH
import Erdos634.Draft.GA2SN
import Erdos634.Draft.GA2ST

namespace Erdos634.GA2SU

open Erdos634.GA2QG

theorem gapA2_of_residual_k (hD3 : PartD3) (hKb : Erdos634.GA2SN.PartKb3Open)
    (hKc : Erdos634.GA2ST.PartKc3Open) : Erdos634.CaseA.R0c15.GapA2 :=
  gapA2_of_parts3 Erdos634.GA2R.partN3060 hD3 Erdos634.GA2SH.partKa
    (Erdos634.GA2SN.partKb3_of_open hKb) (Erdos634.GA2ST.partKc3_of_open hKc)

/-- the residual as ONE hypothesis -/
def GapA2ResidualK : Prop :=
  PartD3 ∧ Erdos634.GA2SN.PartKb3Open ∧ Erdos634.GA2ST.PartKc3Open

theorem gapA2_of_residualK (R : GapA2ResidualK) : Erdos634.CaseA.R0c15.GapA2 :=
  gapA2_of_residual_k R.1 R.2.1 R.2.2

end Erdos634.GA2SU

#print axioms Erdos634.GA2SU.gapA2_of_residual_k
#print axioms Erdos634.GA2SU.gapA2_of_residualK
