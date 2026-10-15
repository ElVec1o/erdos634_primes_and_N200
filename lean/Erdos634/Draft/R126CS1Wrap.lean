import Erdos634.R126CS1

namespace Erdos634.Draft.R126CS1Wrap
open Erdos634.R126CBridge

theorem wrap_slice1_ok :
    ∀ A ∈ slice1, ∀ B ∈ R126Tiling.tiles, A ≠ B → pairOK A B = true :=
  slice1_ok

example : True := trivial
#print axioms wrap_slice1_ok

end Erdos634.Draft.R126CS1Wrap
