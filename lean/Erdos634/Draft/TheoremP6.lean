-- Theorem P with all nine conditional hypotheses of
-- `TheoremPConditional.theoremP_conditional` discharged by Lean theorems:
-- S1 (ScaleBaseBeta), S2 (R-4), C3 (LemmaP), C9 (R8+reduction), C10 (ThmIso).
-- Components used: F1Free, LemmaC, and the cases S4 (R-W) and S5 (R-A).
-- `theoremP_6` therefore takes no hypotheses.
--
-- No sorry, no native_decide.
import Erdos634.Draft.TheoremPConditional
import Erdos634.Draft.ScaleBaseBetaFull
import Erdos634.Draft.RMinus4Full
import Erdos634.Draft.LemmaPProof
import Erdos634.Draft.ThmIsoFull
import Erdos634.Draft.R8F2to4Bridge
import Erdos634.Draft.F1FreeProof
import Erdos634.Draft.LemmaCFinal
import Erdos634.Draft.RWStatementProof
import Erdos634.Draft.RAStatementProof

open scoped Classical

namespace Erdos634.Draft.TheoremP6

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.Draft.TheoremPConditional

theorem theoremP_6 :
    ∀ (N : ℕ) (D : CongruentDissection N), N.Prime → N % 4 = 3 → 3 < N → False :=
  theoremP_conditional
    Erdos634.Draft.LemmaCFinal.lemmaCStatement
    Erdos634.Draft.LemmaPProof.lemmaPStatement
    Erdos634.Draft.ThmIsoFull.thmIso
    Erdos634.Draft.F1FreeProof.f1_free_statement
    Erdos634.Draft.R8F2to4Bridge.r8_reduction_statement
    Erdos634.Draft.ScaleBaseBetaFull.scaleBaseBeta
    Erdos634.Geometry.rMinus4
    Erdos634.Draft.RWStatementProof.rwStatement
    Erdos634.Draft.RAStatementProof.raStatement

end Erdos634.Draft.TheoremP6

#print axioms Erdos634.Draft.TheoremP6.theoremP_6
