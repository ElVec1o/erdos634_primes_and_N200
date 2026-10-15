import Erdos634.S2RPairs8

namespace Erdos634.Draft.S2RPairs8Wrap
open Erdos634.S2RTilingBridge

theorem wrap_pairs_chunk_8 :
    ∀ A ∈ chunk 8, ∀ B ∈ S2RTiling.tiles, A ≠ B → pairOK A B = true :=
  pairs_chunk_8

example : True := trivial
#print axioms wrap_pairs_chunk_8

end Erdos634.Draft.S2RPairs8Wrap
