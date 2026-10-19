/-
Draft/NSQMMainZETW2Witness.lean -- non-vacuity of the S+ extension: `RWChkT2 412` holds, `RWChkT 412` fails; `RWChkT2` is checked by `decide +kernel`.  Negative control: `CN'zETW2 72` fails (72 is a tile count).
Instance walk-through for 412 = 2^2 * 103 = 4 (2*8^2 - 5^2): the only S4 instance is s=2, (e,f)=(5,8) (W_2(5,8)): f=8 <= s e = 10,
e=5 < s(f-e)=6 <= e+1 = 6, s=2<f, so `RWChkT` fails and `RWChkT2` holds.
UNAUDITED.  No sorry, no native_decide.
-/
import Erdos634.Draft.NSQMMainZETW2

set_option maxRecDepth 8000
set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000

namespace Erdos634.Draft.NSQM
open Erdos634.Geometry Erdos634.Draft.NSQRWT Erdos634.Draft.NSQRWT2

theorem not_rwChkT_412 : ¬ Erdos634.Draft.NSQRWT.RWChkT 412 := by decide +kernel
theorem rwChkT2_412 : Erdos634.Draft.NSQRWT2.RWChkT2 412 := by decide +kernel
theorem not_cnzETW2_412 : ¬ CN'zETW2 412 := by decide +kernel  -- the OLD G leaf `GammaChk` fails at 412: use `CN'zETWD2` (D' leaf)
theorem cnzETW2_not_72 : ¬ CN'zETW2 72 := by decide +kernel

end Erdos634.Draft.NSQM

#print axioms Erdos634.Draft.NSQM.rwChkT2_412
