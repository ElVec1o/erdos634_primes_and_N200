-- Draft/CompositeFinal.lean: N = 38 and N = 86: `H1Right` (right tile ⇒ N = 2(x²+y²)) is `H1k.h1Right` (H1kFinal), so the hypothesis `gR`
-- is discharged.  GapR8 (ChainCompositeR8), GapAcomp and HBSimilar (CaseAComposite) are proved.
import Erdos634.Draft.CaseAComposite
import Erdos634.Draft.ChainCompositeR8

namespace Erdos634.Draft.CompositeFinal
open Erdos634.Geometry Erdos634.Draft.ChainComposite

theorem chain_38_final (gR : H1Right 38) (D : CongruentDissection 38) : False :=
  Erdos634.Draft.R8Gen.chain_thirtyeight_R8 Erdos634.CaseA.RComposite.gapAcomp_38
    Erdos634.CaseA.RComposite.hbSimilar_38 gR D

theorem chain_86_final (gR : H1Right 86) (D : CongruentDissection 86) : False :=
  Erdos634.Draft.R8Gen.chain_eightysix_R8 Erdos634.CaseA.RComposite.gapAcomp_86
    Erdos634.CaseA.RComposite.hbSimilar_86 gR D

#print axioms chain_38_final
#print axioms chain_86_final
end Erdos634.Draft.CompositeFinal
