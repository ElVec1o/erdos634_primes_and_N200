import Erdos634.S2RPairs5

namespace Erdos634.Draft.S2RPairs5Wrap
open Erdos634.S2RTilingBridge

theorem wrap_pairs_chunk_5 :
    ∀ A ∈ chunk 5, ∀ B ∈ S2RTiling.tiles, A ≠ B → pairOK A B = true :=
  pairs_chunk_5

example : True := trivial
#print axioms wrap_pairs_chunk_5

end Erdos634.Draft.S2RPairs5Wrap
