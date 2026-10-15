import Erdos634.S2RPairs3

namespace Erdos634.Draft.S2RPairs3Wrap
open Erdos634.S2RTilingBridge

theorem wrap_pairs_chunk_3 :
    ∀ A ∈ chunk 3, ∀ B ∈ S2RTiling.tiles, A ≠ B → pairOK A B = true :=
  pairs_chunk_3

example : True := trivial
#print axioms wrap_pairs_chunk_3

end Erdos634.Draft.S2RPairs3Wrap
