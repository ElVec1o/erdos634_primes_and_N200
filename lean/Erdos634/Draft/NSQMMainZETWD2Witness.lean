/-
Draft/NSQMMainZETWD2Witness.lean -- non-vacuity and instances of the S+ extension of the final chain `CN'zETWD2`.
* `N = 412 = 2^2 (2*8^2 - 5^2)`: the only S4 instance is `W_2(5,8)` (`s = 2`, `(e,f) = (5,8)`, `f <= s e`, `e < s(f-e) = 6 = e+1`, `s < f`).  Old S4 leaf
  `RWChkT 412` FAILS, `RWChkT2 412` holds, `CN'zETWD 412` fails and `CN'zETWD2 412` holds: so 412 is not a tile count, by `not_tile_of_conditionsNSQzETWD2`.
* Further census values (`project working notes`) checked by `decide +kernel` below.
* Negative controls: 72, 143, 320 are tile counts and `CN'zETWD2` fails at each.
Credit: Beeson-Rosu, Paliy, the S+ analysis.  UNAUDITED.  No sorry, no native_decide.
-/
import Erdos634.Draft.NSQMMainZETWD2
import Erdos634.Draft.ThmDChainW

set_option maxRecDepth 8000
set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000

namespace Erdos634.Draft.NSQM
open Erdos634.Geometry

theorem not_rwChkT_412 : ¬ Erdos634.Draft.NSQRWT.RWChkT 412 := by decide +kernel
theorem rwChkT2_412 : Erdos634.Draft.NSQRWT2.RWChkT2 412 := by decide +kernel
theorem not_cnzETWD_412 : ¬ CN'zETWD 412 := by decide +kernel
theorem cnzETWD2_412 : CN'zETWD2 412 := by decide +kernel
theorem not_cnzETWD2_72 : ¬ CN'zETWD2 72 := by decide +kernel
theorem not_cnzETWD2_143 : ¬ CN'zETWD2 143 := by decide +kernel
theorem not_cnzETWD2_320 : ¬ CN'zETWD2 320 := by decide +kernel

theorem no_dissection_412 (D : CongruentDissection 412) : False := not_tile_of_conditionsNSQzETWD2 412 cnzETWD2_412 D

end Erdos634.Draft.NSQM

#print axioms Erdos634.Draft.NSQM.no_dissection_412
