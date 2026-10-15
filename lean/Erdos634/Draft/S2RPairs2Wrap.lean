import Erdos634.S2RPairs2

namespace Erdos634.Draft.S2RPairs2Wrap
open Erdos634.S2RTilingBridge

theorem wrap_pairs_chunk_2 :
    ∀ A ∈ chunk 2, ∀ B ∈ S2RTiling.tiles, A ≠ B → pairOK A B = true :=
  pairs_chunk_2

example : True := trivial
#print axioms wrap_pairs_chunk_2

end Erdos634.Draft.S2RPairs2Wrap
