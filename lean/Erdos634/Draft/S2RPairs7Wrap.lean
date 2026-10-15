import Erdos634.S2RPairs7

namespace Erdos634.Draft.S2RPairs7Wrap
open Erdos634.S2RTilingBridge

theorem wrap_pairs_chunk_7 :
    ∀ A ∈ chunk 7, ∀ B ∈ S2RTiling.tiles, A ≠ B → pairOK A B = true :=
  pairs_chunk_7

example : True := trivial
#print axioms wrap_pairs_chunk_7

end Erdos634.Draft.S2RPairs7Wrap
