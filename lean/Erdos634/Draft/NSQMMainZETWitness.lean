/-
Draft/NSQMMainZETWitness.lean — non-vacuity of `NSQM.CN'zET` (`NSQMMainZET`), and a negative control.
* `cnzET_168`: `CN'zET 168` holds; before `LeafEsqN` the equilateral leaf failed at 168 (the only failing leaf).
* `cnzET_248`: `CN'zET 248` holds; 248 = 2² (2·7² − 6²), the S4 instance (S', e, f) = (2, 6, 7) has S'(f−e) = 2 ≤ 6 = e
  (`cor:thickw`(a)); before `RWChkT` the S4 leaf was the only failing leaf.
* `cnzET_not_72`: 72 = 6² + 6² is a tile count, and `CN'zET 72` fails (negative control).
UNAUDITED.  Formalization debt, NOT /goal progress.  No sorry, no native_decide.
-/
import Erdos634.Draft.NSQMMainZET

set_option maxRecDepth 8000
set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000

namespace Erdos634.Draft.NSQM

open Erdos634.Geometry

theorem cnzET_168 : CN'zET 168 := by decide +kernel
theorem cnzET_248 : CN'zET 248 := by decide +kernel
theorem cnzET_not_72 : ¬ CN'zET 72 := by decide +kernel

/-- the theorem applied: no congruent dissection with 168 or 248 tiles -/
theorem no_dissection_168 (D : CongruentDissection 168) : False := not_tile_of_conditionsNSQzET 168 cnzET_168 D
theorem no_dissection_248 (D : CongruentDissection 248) : False := not_tile_of_conditionsNSQzET 248 cnzET_248 D

end Erdos634.Draft.NSQM

#print axioms Erdos634.Draft.NSQM.cnzET_168
#print axioms Erdos634.Draft.NSQM.cnzET_248
#print axioms Erdos634.Draft.NSQM.no_dissection_248
