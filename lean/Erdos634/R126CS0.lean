import Erdos634.R126CDefs

/-! R126C slice 0: pair check for `A ∈ slice0` against all pieces (one `decide`). -/

namespace Erdos634.R126CBridge

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem slice0_ok : ∀ A ∈ slice0, ∀ B ∈ R126Tiling.tiles, A ≠ B → pairOK A B = true := by
  decide

end Erdos634.R126CBridge
