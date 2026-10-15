import Erdos634.S2RPairs4

namespace Erdos634.Draft.S2RPairs4Wrap
open Erdos634.S2RTilingBridge

theorem wrap_pairs_chunk_4 :
    ∀ A ∈ chunk 4, ∀ B ∈ S2RTiling.tiles, A ≠ B → pairOK A B = true :=
  pairs_chunk_4

example : True := trivial
#print axioms wrap_pairs_chunk_4

end Erdos634.Draft.S2RPairs4Wrap
