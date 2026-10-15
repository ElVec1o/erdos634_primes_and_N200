import Erdos634.S2RPairsDefs
namespace Erdos634.S2RTilingBridge
open Erdos634.Z2Real
-- ordered pairs (A in chunk 11 of 24 tiles) x (B any tile): a working separating edge.
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem pairs_chunk_11 : ∀ A ∈ chunk 11, ∀ B ∈ S2RTiling.tiles, A ≠ B → pairOK A B = true := by
  decide +kernel
#print axioms pairs_chunk_11
end Erdos634.S2RTilingBridge
