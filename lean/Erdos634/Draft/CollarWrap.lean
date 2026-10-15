import Mathlib.Tactic
import Erdos634.Collar

/-!
# Collar decomposition: arithmetic kernel

The collar between the m-target and the apex-anchored (m−2)-target
decomposes as `(m−3)` parallelogram columns + one scale-2 corner triangle + mirror column,
carrying `4(m−1)·N₁` tiles. The cell-count arithmetic is proved in `Collar.lean`.

Four counting facts are kernel-checked:

1. **`collar_cells`**: (k+2)²=k²+4(k+1), so the collar band is 4(m−1) unit cells.
2. **`collar_assembly`**: 4+4(m−3)+4=4(m−1) for m≥3, so the three blocks fill the collar.
3. **`collar_count_12`**: 11((k+2)²)=11k²+44(k+1), the (1,2) member in tiles.
4. **`collar_count`**: N₁((k+2)²)=N₁k²+4N₁(k+1), the general base-β member.

The geometric decomposition (union of dissections, flush interfaces) has no `Dissection`-level
statement here.  `UnionDissection.unionCongruentDissection` exists but is not applied to the collar.

Cell and tile count arithmetic only; no `sorry`, no axioms.
-/

namespace Erdos634.Draft.CollarWrap

open Erdos634.Collar

/-- Collar cell count: (k+2)² = k² + 4(k+1). -/
theorem collar_cells_wrap (k : ℕ) : (k + 2) * (k + 2) = k * k + 4 * (k + 1) :=
  collar_cells k

/-- Collar assembly: 4 + 4(m−3) + 4 = 4(m−1) for m ≥ 3. -/
theorem collar_assembly_wrap (m : ℕ) (h : 3 ≤ m) : 4 + 4 * (m - 3) + 4 = 4 * (m - 1) :=
  collar_assembly m h

/-- (1,2) member collar tile count: 11·(k+2)² = 11·k² + 44·(k+1). -/
theorem collar_count_12_wrap (k : ℕ) : 11 * ((k + 2) * (k + 2)) = 11 * (k * k) + 44 * (k + 1) :=
  collar_count_12 k

/-- General base-β member: N₁·(k+2)² = N₁·k² + 4·N₁·(k+1). -/
theorem collar_count_general (N₁ k : ℕ) :
    N₁ * ((k + 2) * (k + 2)) = N₁ * (k * k) + 4 * N₁ * (k + 1) :=
  collar_count N₁ k

/-- Non-vacuity: at k=0, collar_cells gives 4 = 0 + 4. -/
theorem collar_cells_witness : (0 + 2) * (0 + 2) = 0 * 0 + 4 * (0 + 1) := by norm_num

#print axioms collar_cells_wrap
#print axioms collar_assembly_wrap
#print axioms collar_count_12_wrap

end Erdos634.Draft.CollarWrap
