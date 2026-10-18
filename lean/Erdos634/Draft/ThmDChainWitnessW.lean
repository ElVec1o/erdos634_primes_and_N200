import Erdos634.Draft.ThmDChainW

/-!
# Non-vacuity of the final chain `CN'zETWD` (D' leaf + S5 word leaf)  
* `N = 276`: `CN'zETWD 276` holds; neither leaf alone suffices: `CN'zETD 276` fails (S5p leaf) and `CN'zETW 276` fails (old G leaf),
  so 276 is excluded only by Theorem D' and the S5 word leaf TOGETHER.
* `N = 279`, `204`, `268`: likewise (`CN'zETWD` holds, `CN'zETD` and `CN'zETW` fail).  (Census in [200,500): no value is in `CN'zETD` but not `CN'zET`, since the old S5 leaf fails there.)
* Negative controls: 72, 143, 320 are tile counts (kernel-checked tilings exist), and `CN'zETWD` fails at each.
-/

set_option maxRecDepth 8000
set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000

namespace Erdos634.Draft.NSQM

open Erdos634.Geometry

theorem cnzETWD_276 : CN'zETWD 276 := by decide +kernel
theorem not_cnzETD_276 : ¬ CN'zETD 276 := by decide +kernel
theorem not_cnzETW_276 : ¬ CN'zETW 276 := by decide +kernel
theorem cnzETWD_279 : CN'zETWD 279 := by decide +kernel
theorem not_cnzETD_279 : ¬ CN'zETD 279 := by decide +kernel
theorem not_cnzETW_279 : ¬ CN'zETW 279 := by decide +kernel
theorem cnzETWD_204 : CN'zETWD 204 := by decide +kernel
theorem not_cnzETD_204 : ¬ CN'zETD 204 := by decide +kernel
theorem not_cnzETW_204 : ¬ CN'zETW 204 := by decide +kernel
theorem cnzETWD_268 : CN'zETWD 268 := by decide +kernel
theorem not_cnzETD_268 : ¬ CN'zETD 268 := by decide +kernel
theorem not_cnzETW_268 : ¬ CN'zETW 268 := by decide +kernel
theorem not_cnzETWD_72 : ¬ CN'zETWD 72 := by decide +kernel
theorem not_cnzETWD_143 : ¬ CN'zETWD 143 := by decide +kernel
theorem not_cnzETWD_320 : ¬ CN'zETWD 320 := by decide +kernel

theorem no_dissection_276 (D : CongruentDissection 276) : False := not_tile_of_conditionsNSQzETWD 276 cnzETWD_276 D
theorem no_dissection_279_w (D : CongruentDissection 279) : False := not_tile_of_conditionsNSQzETWD 279 cnzETWD_279 D

end Erdos634.Draft.NSQM

#print axioms Erdos634.Draft.NSQM.no_dissection_276
#print axioms Erdos634.Draft.NSQM.no_dissection_279_w
#print axioms Erdos634.Draft.ThmD.thmDStatement_geo
#print axioms Erdos634.Draft.NSQM.not_tile_of_conditionsNSQzETWD
