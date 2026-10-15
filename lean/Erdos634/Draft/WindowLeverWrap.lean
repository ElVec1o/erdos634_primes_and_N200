import Erdos634.WindowLever

namespace Erdos634.Draft.WindowLeverWrap
open Erdos634.WindowLever

theorem wrap_window_bound_vacuous_if_empty {Tiling : Type} {P : Tiling → Prop}
    (hempty : ¬ Nonempty Tiling) : ∀ t : Tiling, P t :=
  window_bound_vacuous_if_empty hempty

example : True := trivial
#check @wrap_window_bound_vacuous_if_empty

end Erdos634.Draft.WindowLeverWrap
