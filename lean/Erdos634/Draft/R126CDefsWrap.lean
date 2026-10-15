import Erdos634.R126CDefs

namespace Erdos634.Draft.R126CDefsWrap
open Erdos634.R126CBridge

theorem wrap_cover : ∀ A ∈ R126Tiling.tiles,
    A ∈ slice0 ∨ A ∈ slice1 ∨ A ∈ slice2 ∨ A ∈ slice3 ∨ A ∈ slice4 ∨ A ∈ slice5 :=
  cover

example : True := trivial
#print axioms wrap_cover

end Erdos634.Draft.R126CDefsWrap
