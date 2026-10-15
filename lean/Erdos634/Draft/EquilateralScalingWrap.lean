import Erdos634.EquilateralScaling

namespace Erdos634.Draft.EquilateralScalingWrap
open Erdos634.EquilateralScaling

theorem wrap_achievable_upward (achievable : ℕ → Prop)
    (up : ∀ j l : ℕ, achievable j → achievable (l * j)) (k m : ℕ) (hk : achievable k) :
    achievable (m * k) :=
  achievable_upward achievable up k m hk

example : True := trivial
#print axioms wrap_achievable_upward

end Erdos634.Draft.EquilateralScalingWrap
