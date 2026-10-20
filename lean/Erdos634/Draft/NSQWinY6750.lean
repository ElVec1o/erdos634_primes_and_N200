/-
Draft/NSQWinY6750.lean -- `no_dissection_y6750` via the fully windowed chain `CN'zETWD6` (`NSQWin3`). Credit: Beeson-Rosu, Paliy, the S+ analysis. UNAUDITED. No sorry, no native_decide.
-/
import Erdos634.Draft.NSQWin3

set_option maxRecDepth 8000
set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000

namespace Erdos634.Draft.NSQM
open Erdos634.Geometry

theorem cnzETWD6_6750 : CN'zETWD6 6750 := by decide +kernel
theorem no_dissection_y6750 (D : CongruentDissection 6750) : False := not_tile_of_conditionsNSQzETWD6 6750 cnzETWD6_6750 D

end Erdos634.Draft.NSQM

#print axioms Erdos634.Draft.NSQM.no_dissection_y6750
