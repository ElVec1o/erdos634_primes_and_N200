import Erdos634.S2RPairsDefs
namespace Erdos634.S2RTilingBridge
open Erdos634.Z2Real
-- ordered pairs (A in chunk 10 of 24 tiles) x (B any tile): a working separating edge.
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem pairs_chunk_10 : ∀ A ∈ chunk 10, ∀ B ∈ S2RTiling.tiles, A ≠ B → pairOK A B = true := by
  decide +kernel
#print axioms pairs_chunk_10
end Erdos634.S2RTilingBridge
