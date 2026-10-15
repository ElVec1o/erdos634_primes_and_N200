import Erdos634.S2RPairs6

namespace Erdos634.Draft.S2RPairs6Wrap
open Erdos634.S2RTilingBridge

theorem wrap_pairs_chunk_6 :
    ∀ A ∈ chunk 6, ∀ B ∈ S2RTiling.tiles, A ≠ B → pairOK A B = true :=
  pairs_chunk_6

example : True := trivial
#print axioms wrap_pairs_chunk_6

end Erdos634.Draft.S2RPairs6Wrap
