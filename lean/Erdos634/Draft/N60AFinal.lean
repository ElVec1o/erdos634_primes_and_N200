/-
Draft/N60AFinal.lean -- N = 60: `chain_60_four` : the chain of `N60AChain.chain_60_final'` with the Case A leaf `GapA 60` DISCHARGED by `N60A.gapA60`
(constant-60 area kill, `N60AF`).  Exactly FOUR residual hypotheses remain:
    CaseGClosed 60, GapE60 60, GapE120 60, RAStatementNsq 60
  CONDITIONAL on four leaves; NOT an exclusion of 60. ***
-/
import Erdos634.Draft.N60AChain
import Erdos634.Draft.N60AF

namespace Erdos634.Draft.N60A

open Erdos634.Geometry Erdos634.Draft.Chain15 Erdos634.Draft.ChainComposite Erdos634.Draft.NSQRA

theorem chain_60_four (gG : CaseGClosed 60) (gE60 : GapE60 60) (gE120 : GapE120 60)
    (gS5 : RAStatementNsq 60) (D : CongruentDissection 60) : False :=
  chain_60_final' Erdos634.N60A.gapA60 gG gE60 gE120 gS5 D

end Erdos634.Draft.N60A

#print axioms Erdos634.Draft.N60A.chain_60_four
