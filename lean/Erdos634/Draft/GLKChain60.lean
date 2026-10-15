import Erdos634.Draft.GLKBridge
import Erdos634.Draft.N60AChain

/-!
# GLK(b): `chain_60_final_G` — N = 60 modulo FOUR named leaves (CaseGClosed 60 discharged by `GLKBridge.caseG_60`) conditional; NOT an exclusion of 60.  Residual: `GapA 60`, `GapE60 60`, `GapE120 60`, `RAStatementNsq 60`.
(`GapF1`, `GapR8`, `RW` already discharged inside `chain_60_final'`; the prompt's list names GapR8/GapF1/RW60 as residual
but in this repo they are closed by `decide +kernel` checks.)
-/

namespace Erdos634.GLK

open Erdos634.Geometry Erdos634.Draft.TheoremPConditional Erdos634.Draft.Chain15 Erdos634.Draft.ChainComposite
  Erdos634.Draft.CompositeGen2 Erdos634.Draft.CompositeFinal3 Erdos634.Draft.NSQRA Erdos634.Draft.NSQMain

theorem chain_60_final_G (gA : GapA 60) (gE60 : GapE60 60) (gE120 : GapE120 60)
    (gS5 : RAStatementNsq 60) (D : CongruentDissection 60) : False :=
  Erdos634.Draft.N60A.chain_60_final' gA caseG_60 gE60 gE120 gS5 D

end Erdos634.GLK

#print axioms Erdos634.GLK.chain_60_final_G
