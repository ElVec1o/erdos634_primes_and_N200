import Erdos634.R126CDefs

/-! R126C slice 2: pair check for `A ∈ slice2` against all pieces (one `decide`). -/

namespace Erdos634.R126CBridge

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem slice2_ok : ∀ A ∈ slice2, ∀ B ∈ R126Tiling.tiles, A ≠ B → pairOK A B = true := by
  decide

end Erdos634.R126CBridge
