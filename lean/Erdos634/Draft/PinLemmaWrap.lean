import Erdos634.PinLemma

namespace Erdos634.Draft.PinLemmaWrap
open Erdos634.PinLemma

theorem wrap_beta_tile_dies (f x y z : ℕ) (hf : 3 ≤ f)
    (hcover : x * f + y * (f * f - 1) + z * (f * f) = f * f - 1 - f ∨
              x * f + y * (f ^ 2 - 1) + z * f ^ 2 = 1) : False :=
  beta_tile_dies f x y z hf hcover

example : True := trivial
#print axioms wrap_beta_tile_dies

end Erdos634.Draft.PinLemmaWrap
