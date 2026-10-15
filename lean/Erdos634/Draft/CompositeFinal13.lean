/-
Draft/CompositeFinal13.lean — N = 87 hypothesis-free: the single residual `E60Pair 87 29 9` of `CompositeFinal10.chain_87_final'`
is discharged by `E60Mod9C.e60Pair_87` (the mod-9 obstruction of the direction-class cancellation, `E60Mod9A/B/C`).  No sorry, no native_decide. ***
-/
import Erdos634.Draft.E60Mod9C
import Erdos634.Draft.CompositeFinal10

namespace Erdos634.Draft.CompositeFinal13

open Erdos634.Geometry

/-- **N = 87: no residual hypothesis.** -/
theorem chain_87_final'' (D : CongruentDissection 87) : False :=
  Erdos634.Draft.CompositeFinal10.chain_87_final' Erdos634.Draft.E60Mod9.e60Pair_87 D

end Erdos634.Draft.CompositeFinal13

#print axioms Erdos634.Draft.CompositeFinal13.chain_87_final''
