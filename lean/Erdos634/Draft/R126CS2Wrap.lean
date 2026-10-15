import Erdos634.R126CS2

namespace Erdos634.Draft.R126CS2Wrap
open Erdos634.R126CBridge

theorem wrap_slice2_ok :
    ∀ A ∈ slice2, ∀ B ∈ R126Tiling.tiles, A ≠ B → pairOK A B = true :=
  slice2_ok

example : True := trivial
#print axioms wrap_slice2_ok

end Erdos634.Draft.R126CS2Wrap
