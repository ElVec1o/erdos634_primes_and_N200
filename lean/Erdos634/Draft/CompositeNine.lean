-- Draft/CompositeNine.lean — NINE composite exclusions as HYPOTHESIS-FREE theorems: N = 14, 22, 38, 42, 46, 62, 66, 78, 86.
-- Each chain's last residual `H1Right N` is discharged by `H1k.h1Right N` (right-tile branch, proved for ALL N).
import Erdos634.Draft.H1kFinal
import Erdos634.Draft.CompositeFinal
import Erdos634.Draft.CompositeFinal2
import Erdos634.Draft.CompositeFinal3
import Erdos634.Draft.CompositeFinal4
import Erdos634.Draft.CompositeFinal5
import Erdos634.Draft.ChainCompositeR8b

namespace Erdos634.Draft.CompositeNine
open Erdos634.Geometry

theorem not_tile_14 (D : CongruentDissection 14) : False :=
  Erdos634.Draft.CompositeFinal2.chain_14_final (Erdos634.Draft.H1k.h1Right 14) D
theorem not_tile_22 (D : CongruentDissection 22) : False :=
  Erdos634.Draft.CompositeFinal5.chain_22_H1only (Erdos634.Draft.H1k.h1Right 22) D
theorem not_tile_38 (D : CongruentDissection 38) : False :=
  Erdos634.Draft.CompositeFinal.chain_38_final (Erdos634.Draft.H1k.h1Right 38) D
theorem not_tile_42 (D : CongruentDissection 42) : False :=
  Erdos634.Draft.CompositeFinal5.chain_42_H1only (Erdos634.Draft.H1k.h1Right 42) D
theorem not_tile_46 (D : CongruentDissection 46) : False :=
  Erdos634.Draft.CompositeFinal3.chain_46_final (Erdos634.Draft.H1k.h1Right 46) D
theorem not_tile_62 (D : CongruentDissection 62) : False :=
  Erdos634.Draft.CompositeFinal2.chain_62_final (Erdos634.Draft.H1k.h1Right 62) D
theorem not_tile_66 (D : CongruentDissection 66) : False :=
  Erdos634.Draft.CompositeFinal4.chain_66_H1only (Erdos634.Draft.H1k.h1Right 66) D
theorem not_tile_78 (D : CongruentDissection 78) : False :=
  Erdos634.Draft.R8Gen2.chain_78_R8 (Erdos634.Draft.H1k.h1Right 78) D
theorem not_tile_86 (D : CongruentDissection 86) : False :=
  Erdos634.Draft.CompositeFinal.chain_86_final (Erdos634.Draft.H1k.h1Right 86) D

#print axioms not_tile_14
#print axioms not_tile_22
#print axioms not_tile_38
#print axioms not_tile_42
#print axioms not_tile_46
#print axioms not_tile_62
#print axioms not_tile_66
#print axioms not_tile_78
#print axioms not_tile_86
end Erdos634.Draft.CompositeNine
