-- Draft/ChainGapA60.lean — N = 60 chain with GapA 60 discharged.
-- `chain_60_final_GA` = `chain_60_final_G` with `Erdos634.N60A.gapA60` plugged in.
-- It is still conditional on three hypotheses: GapE60 60, GapE120 60, RAStatementNsq 60.
import Erdos634.Draft.GLKChain60
import Erdos634.Draft.N60AF

namespace Erdos634.Draft.ChainGapA60

open Erdos634.Geometry Erdos634.Draft.Chain15 Erdos634.Draft.NSQRA

theorem chain_60_final_GA (gE60 : GapE60 60) (gE120 : GapE120 60)
    (gS5 : RAStatementNsq 60) (D : CongruentDissection 60) : False :=
  Erdos634.GLK.chain_60_final_G Erdos634.N60A.gapA60 gE60 gE120 gS5 D

end Erdos634.Draft.ChainGapA60

#print axioms Erdos634.Draft.ChainGapA60.chain_60_final_GA
