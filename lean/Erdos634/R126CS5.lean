import Erdos634.R126CDefs

/-! R126C slice 5: pair check for `A ∈ slice5` against all pieces (one `decide`). -/

namespace Erdos634.R126CBridge

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem slice5_ok : ∀ A ∈ slice5, ∀ B ∈ R126Tiling.tiles, A ≠ B → pairOK A B = true := by
  decide

end Erdos634.R126CBridge
