import Erdos634.StripIteration

namespace Erdos634.Draft.StripIterationWrap
open Erdos634.StripIteration Erdos634.Geometry

theorem wrap_interior_rigidity_of_predecessor {N : ℕ}
    (D : CongruentDissection N)
    (idx : ℕ → Fin N)
    (base : ¬ (D.tile (idx 0)).Reflected D.model)
    (step : ∀ j, D.UnreflectedAt (idx j) → ¬ (D.tile (idx (j + 1))).Reflected D.model) :
    ∀ j, D.UnreflectedAt (idx j) :=
  interior_rigidity_of_predecessor D idx base step

example : True := trivial
#check @wrap_interior_rigidity_of_predecessor

end Erdos634.Draft.StripIterationWrap
