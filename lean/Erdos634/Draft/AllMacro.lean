-- Draft/AllMacro.lean — aggregate of the macro-piece / lowered-tail modules (DEBT_A, 2026-10-19).  Not imported by All.
import Erdos634.Draft.TileCountFamilies
import Erdos634.Draft.TM375
import Erdos634.Draft.TM540
import Erdos634.Draft.TM735
import Erdos634.Draft.TM825
import Erdos634.Draft.TM630
import Erdos634.Draft.TM1120
import Erdos634.Draft.TM1750
import Erdos634.Draft.TM3864
import Erdos634.Draft.TM8694
import Erdos634.Draft.TM9940
import Erdos634.Draft.TM15456
import Erdos634.Draft.TM22365
import Erdos634.Draft.TM24150
import Erdos634.Draft.TM34776
import Erdos634.Draft.TM47334
import Erdos634.Draft.TM61824
import Erdos634.Draft.TM96600
import Erdos634.Draft.TM116886
import Erdos634.Draft.TM139104
import Erdos634.Draft.TM163254
import Erdos634.Draft.TM189336
import Erdos634.Draft.TM217350
import Erdos634.Draft.TM247296
import Erdos634.Draft.TM279174
import Erdos634.Draft.TM312984
import Erdos634.Draft.T62125
import Erdos634.Draft.CollarFam5
import Erdos634.Draft.CollarFam17

namespace Erdos634.Draft.AllMacro
open Erdos634.Draft.TileCountFamilies (TileCount tileCount_scale)

/-- `78246 = 3²·8694` (966·9²). -/
theorem tileCount_78246 : TileCount 78246 := by
  simpa using tileCount_scale Erdos634.Draft.TM8694.tileCount_8694 (k := 3) (by norm_num)

end Erdos634.Draft.AllMacro

#print axioms Erdos634.Draft.AllMacro.tileCount_78246
