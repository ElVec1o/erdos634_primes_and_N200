import Erdos634.S2RPairs13

namespace Erdos634.Draft.S2RPairs13Wrap
open Erdos634.S2RTilingBridge

theorem wrap_pairs_chunk_13 :
    ∀ A ∈ chunk 13, ∀ B ∈ S2RTiling.tiles, A ≠ B → pairOK A B = true :=
  pairs_chunk_13

example : True := trivial
#print axioms wrap_pairs_chunk_13

end Erdos634.Draft.S2RPairs13Wrap
