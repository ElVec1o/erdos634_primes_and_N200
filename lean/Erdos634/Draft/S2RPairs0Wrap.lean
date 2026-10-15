import Erdos634.S2RPairs0

namespace Erdos634.Draft.S2RPairs0Wrap
open Erdos634.S2RTilingBridge

theorem wrap_pairs_chunk_0 :
    ∀ A ∈ chunk 0, ∀ B ∈ S2RTiling.tiles, A ≠ B → pairOK A B = true :=
  pairs_chunk_0

example : True := trivial
#print axioms wrap_pairs_chunk_0

end Erdos634.Draft.S2RPairs0Wrap
