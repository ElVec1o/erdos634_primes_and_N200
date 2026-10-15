import Erdos634.S2RPairs9

namespace Erdos634.Draft.S2RPairs9Wrap
open Erdos634.S2RTilingBridge

theorem wrap_pairs_chunk_9 :
    ∀ A ∈ chunk 9, ∀ B ∈ S2RTiling.tiles, A ≠ B → pairOK A B = true :=
  pairs_chunk_9

example : True := trivial
#print axioms wrap_pairs_chunk_9

end Erdos634.Draft.S2RPairs9Wrap
