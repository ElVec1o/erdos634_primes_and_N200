/-
AllV3.lean -- aggregator for the modules added in release v3.0.  Does NOT import `Erdos634.All`; no search certificate `Refl.M*` in the
import closure.  Build through `code/lakeone_at.sh` (modules one at a time).  Contents: Conjecture C existence half (`AllConjC`),
the collar family (`CollarUp`, `CollarFam5`, `CollarFam17`), template squares (`TemplateSquares`), macro-piece tilings (`AllMacro`),
the 13 W-below tilings (`AllWBelow`), the W-tilable closures (`AllDebtB`), and Theorem W (`AllThmW`).
-/
import Erdos634.AllConjC
import Erdos634.Draft.CollarUp
import Erdos634.Draft.CollarFam5
import Erdos634.Draft.CollarFam17
import Erdos634.Draft.TemplateSquares
import Erdos634.Draft.T62125
import Erdos634.Draft.AllMacro
import Erdos634.Draft.AllWBelow
import Erdos634.Draft.AllDebtB
import Erdos634.Draft.AllThmW
