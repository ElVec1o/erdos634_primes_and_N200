import Erdos634.S2RPairs1

namespace Erdos634.Draft.S2RPairs1Wrap
open Erdos634.S2RTilingBridge

theorem wrap_pairs_chunk_1 :
    ∀ A ∈ chunk 1, ∀ B ∈ S2RTiling.tiles, A ≠ B → pairOK A B = true :=
  pairs_chunk_1

example : True := trivial
#print axioms wrap_pairs_chunk_1

end Erdos634.Draft.S2RPairs1Wrap
