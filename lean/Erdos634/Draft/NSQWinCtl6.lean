/-
Draft/NSQWinCtl6.lean -- NON-VACUITY controls for the fully windowed chain `CN'zETWD6` (`NSQWin3`): it must FAIL at known tile counts
(72, 143, 320, 375, 540, 1860 = 465 * 2^2, 4185 = 465 * 3^2, 7440 = 465 * 4^2, 63, 1029), else the windowed checks could be vacuously true.
Also positive controls: the chain holds at the excluded values 270 and 412 (so it is neither always-false nor always-true).
-/
import Erdos634.Draft.NSQWin3

set_option maxRecDepth 8000
set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000

namespace Erdos634.Draft.NSQM

theorem ctl6_72 : ¬ CN'zETWD6 72 := by decide +kernel
theorem ctl6_143 : ¬ CN'zETWD6 143 := by decide +kernel
theorem ctl6_320 : ¬ CN'zETWD6 320 := by decide +kernel
theorem ctl6_375 : ¬ CN'zETWD6 375 := by decide +kernel
theorem ctl6_540 : ¬ CN'zETWD6 540 := by decide +kernel
theorem ctl6_1860 : ¬ CN'zETWD6 1860 := by decide +kernel
theorem ctl6_4185 : ¬ CN'zETWD6 4185 := by decide +kernel
theorem ctl6_7440 : ¬ CN'zETWD6 7440 := by decide +kernel
theorem ctl6_63 : ¬ CN'zETWD6 63 := by decide +kernel
theorem ctl6_1029 : ¬ CN'zETWD6 1029 := by decide +kernel
theorem pos6_270 : CN'zETWD6 270 := by decide +kernel
theorem pos6_412 : CN'zETWD6 412 := by decide +kernel

end Erdos634.Draft.NSQM
#print axioms Erdos634.Draft.NSQM.ctl6_7440
