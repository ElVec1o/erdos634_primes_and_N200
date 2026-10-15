import Erdos634.RunOrientation

namespace Erdos634.Draft.RunOrientationWrap
open Erdos634.RunOrientation Erdos634.Inflation Erdos634.Inflation.Orient

theorem wrap_corner_anchored_run_last (L : List Orient)
    (h : L.Chain' (fun l r => admissiblePair l r = true))
    (hhead : L.head? = some Orient.BG) (hne : L ≠ []) :
    L.getLast hne = Orient.BG :=
  corner_anchored_run_last L h hhead hne

example : True := trivial
#print axioms wrap_corner_anchored_run_last

end Erdos634.Draft.RunOrientationWrap
