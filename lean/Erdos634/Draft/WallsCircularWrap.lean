import Erdos634.WallsCircular

namespace Erdos634.Draft.WallsCircularWrap
open Erdos634.WallsCircular

theorem wrap_conditional_is_vacuous {Tiling : Type*} (WestComplete : Tiling → Prop)
    (never : ∀ T, ¬ WestComplete T) (walls : ∀ T, WestComplete T) : IsEmpty Tiling :=
  conditional_is_vacuous WestComplete never walls

example : True := trivial
#check @wrap_conditional_is_vacuous

end Erdos634.Draft.WallsCircularWrap
