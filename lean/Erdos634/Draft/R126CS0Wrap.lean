import Erdos634.R126CS0

namespace Erdos634.Draft.R126CS0Wrap
open Erdos634.R126CBridge

theorem wrap_slice0_ok :
    ∀ A ∈ slice0, ∀ B ∈ R126Tiling.tiles, A ≠ B → pairOK A B = true :=
  slice0_ok

example : True := trivial
#print axioms wrap_slice0_ok

end Erdos634.Draft.R126CS0Wrap
