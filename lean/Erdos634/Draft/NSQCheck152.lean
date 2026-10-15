/- Draft/NSQCheck152.lean — Lean exclusion of N=152 via NSQMain.
152 = 8 × 19; RAShape 152 holds since 152 % 8 = 0, Squarefree 19 = true, 19 % 2 = 1.
NQChk 152: 152 = 2² × 38, 38 squarefree, 38 % 4 = 2.  EllChk2: prime 19 ≥ 7, 19 ∣ 152, 19² ∤ 152.
No sorry, no native_decide.
-/
import Erdos634.Draft.NSQMain
set_option maxRecDepth 8000
set_option maxHeartbeats 800000
namespace Erdos634.Draft.NSQCheck152
open Erdos634.Geometry Erdos634.Draft.NSQMain

-- Build CN 152 component-by-component to avoid kernel resource limits on the conjunction
theorem CN_152 : CN 152 := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
         by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
         by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
         by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem not_tile_152 (D : CongruentDissection 152) : False := not_tile_of_nsq 152 CN_152 D

end Erdos634.Draft.NSQCheck152

