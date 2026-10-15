import Erdos634.R126CS3

namespace Erdos634.Draft.R126CS3Wrap
open Erdos634.R126CBridge

theorem wrap_slice3_ok :
    ∀ A ∈ slice3, ∀ B ∈ R126Tiling.tiles, A ≠ B → pairOK A B = true :=
  slice3_ok

example : True := trivial
#print axioms wrap_slice3_ok

end Erdos634.Draft.R126CS3Wrap
