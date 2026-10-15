import Erdos634.S2RPairs12

namespace Erdos634.Draft.S2RPairs12Wrap
open Erdos634.S2RTilingBridge

theorem wrap_pairs_chunk_12 :
    ∀ A ∈ chunk 12, ∀ B ∈ S2RTiling.tiles, A ≠ B → pairOK A B = true :=
  pairs_chunk_12

example : True := trivial
#print axioms wrap_pairs_chunk_12

end Erdos634.Draft.S2RPairs12Wrap
