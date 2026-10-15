-- No sorry, no native_decide, no axioms.
-- Generic rewriting lemmas so that `pairsOK clusters seps = some []` can be assembled from PER-PAIR facts `clSep P Q cl_i cl_j = true`
-- proved in separate modules (the Cert module then never evaluates a separation).
import Erdos634.Draft.G3CCert

namespace Erdos634.Draft.G3OPairs

open Erdos634.Draft.G3CCert

theorem rowOK_cons_true {P Q : LP} {c d : Bsp} {ds : List Bsp} {s : List (LP × LP)}
    (h : clSep P Q c d = true) : rowOK c (d :: ds) ((P, Q) :: s) = rowOK c ds s := by
  simp [rowOK, h]

theorem rowOK_nil (c : Bsp) (s : List (LP × LP)) : rowOK c [] s = some s := by
  simp [rowOK]

theorem pairsOK_cons_some (c : Bsp) (cs : List Bsp) (s s' : List (LP × LP)) (h : rowOK c cs s = some s') :
    pairsOK (c :: cs) s = pairsOK cs s' := by
  simp [pairsOK, h]

theorem pairsOK_nil (s : List (LP × LP)) : pairsOK [] s = some s := by
  simp [pairsOK]

end Erdos634.Draft.G3OPairs
