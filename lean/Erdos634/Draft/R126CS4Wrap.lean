import Erdos634.R126CS4

namespace Erdos634.Draft.R126CS4Wrap
open Erdos634.R126CBridge

theorem wrap_slice4_ok :
    ∀ A ∈ slice4, ∀ B ∈ R126Tiling.tiles, A ≠ B → pairOK A B = true :=
  slice4_ok

example : True := trivial
#print axioms wrap_slice4_ok

end Erdos634.Draft.R126CS4Wrap
