import Erdos634.R126CDefs

/-! R126C slice 4: pair check for `A ∈ slice4` against all pieces (one `decide`). -/

namespace Erdos634.R126CBridge

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem slice4_ok : ∀ A ∈ slice4, ∀ B ∈ R126Tiling.tiles, A ≠ B → pairOK A B = true := by
  decide

end Erdos634.R126CBridge
