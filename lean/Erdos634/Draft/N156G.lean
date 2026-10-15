/-
Draft/N156G.lean -- `156` after the `γ = 2α` certificate.

`GPairs156.gpair_6_26` (certificate `Refl.MG156`, 87,352 nodes, kernel-checked) discharges the third
hypothesis of `OpenRed.not_tile_156_of`:

    theorem not_tile_156_of_two (h1 : S1Inst 2 3 4) (h2 : S5Inst 2 5 8) (D : CongruentDissection 156) : False

The instances `S1Inst 2 3 4` and `S5Inst 2 5 8` remain as hypotheses.  No sorry, no native_decide.
-/
import Erdos634.Draft.OpenReductionsNsq
import Erdos634.Draft.GPairs156

namespace Erdos634.Draft.N156G

open Erdos634.Geometry Erdos634.Draft.NSQM Erdos634.Draft.OpenRed Erdos634.Draft.CompositeFinal4

/-- `156` from its two remaining instances: the base-β member `(3, 4)` at scale `2` and the S5 instance `(2, 5, 8)` -/
theorem not_tile_156_of_two (h1 : S1Inst 2 3 4) (h2 : S5Inst 2 5 8) (D : CongruentDissection 156) : False :=
  not_tile_156_of (@h1) (@h2) Erdos634.Draft.GPairs156.gpair_6_26 D

end Erdos634.Draft.N156G

#print axioms Erdos634.Draft.N156G.not_tile_156_of_two
