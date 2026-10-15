import Erdos634.OrientationGauge

namespace Erdos634.Draft.OrientationGaugeWrap
open Erdos634.Geometry

theorem wrap_interior_rigidity_of_adjacent {N : ℕ} (D : CongruentDissection N) (idx : ℕ → Fin N)
    (adj : ∀ j, ¬ (D.tile (idx (j + 1))).OppOrient (D.tile (idx j))) :
    ∀ j, (D.tile (idx j)).EqOrient (D.tile (idx 0)) :=
  interior_rigidity_of_adjacent D idx adj

example : True := trivial
#print axioms wrap_interior_rigidity_of_adjacent

end Erdos634.Draft.OrientationGaugeWrap
