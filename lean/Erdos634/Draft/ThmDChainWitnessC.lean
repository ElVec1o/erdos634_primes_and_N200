import Erdos634.Draft.ThmDChain

/-!
# Theorem D': non-vacuity of the chain `CN'zETD`, part C  
Negative controls: 72 = 6^2 + 6^2 and 143 (kernel-checked tiling of (39,49,55) by (3,5,7)) are tile counts; `CN'zETD` fails at both.
-/

set_option maxRecDepth 8000
set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000

namespace Erdos634.Draft.NSQM

open Erdos634.Geometry

theorem not_cnzETD_72 : ¬ CN'zETD 72 := by decide +kernel
theorem not_cnzETD_143 : ¬ CN'zETD 143 := by decide +kernel
theorem not_cnzETD_320 : ¬ CN'zETD 320 := by decide +kernel

end Erdos634.Draft.NSQM
