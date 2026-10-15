import Erdos634.R126CS5

namespace Erdos634.Draft.R126CS5Wrap
open Erdos634.R126CBridge

theorem wrap_slice5_ok :
    ∀ A ∈ slice5, ∀ B ∈ R126Tiling.tiles, A ≠ B → pairOK A B = true :=
  slice5_ok

example : True := trivial
#print axioms wrap_slice5_ok

end Erdos634.Draft.R126CS5Wrap
