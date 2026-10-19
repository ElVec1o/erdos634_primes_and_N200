/-
Draft/NSQMMainZETWD3W270.lean -- instances of the final chain `CN'zETWD3` (`NSQMMainZETWD3`): the A leaf `GAU.gapA_sq` and the S1 leaf `S1t2Chk`.
* `270 = 30 * 3^2`: only failing census leaf is A; `no_dissection_270`. (750 and 963 are NOT in this release: their leaf checks exceed the memory budget.)
* Negative controls (tile counts, `CN'zETWD3` must FAIL): 72, 143, 320, 540 (`15 * 6^2`, tile count), 375 (`15 * 5^2`).
Credit: Beeson-Rosu, Paliy, the S+ analysis, the GAP4 analysis.  UNAUDITED.  No sorry, no native_decide.
-/
import Erdos634.Draft.NSQMMainZETWD3

set_option maxRecDepth 8000
set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000

namespace Erdos634.Draft.NSQM
open Erdos634.Geometry

theorem cnzETWD3_270 : CN'zETWD3 270 := by decide +kernel
theorem no_dissection_270 (D : CongruentDissection 270) : False := not_tile_of_conditionsNSQzETWD3 270 cnzETWD3_270 D

end Erdos634.Draft.NSQM

#print axioms Erdos634.Draft.NSQM.no_dissection_270
