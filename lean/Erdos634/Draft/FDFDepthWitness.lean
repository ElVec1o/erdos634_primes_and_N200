import Erdos634.Draft.L3MReal

/-!
# FDF depth-window witness (arithmetic control only)

The depth hypotheses of `l3m_band` / `l3m_terminal` (Draft/L3MReal.lean), at
`(e, f) = (2, 5)`, `k' = 0`, `w0 = 2`, `L' = k' + 1 + w0 = 3`, hold arithmetically.
`cb e f = f² / (f² - e²)` (Draft/MirrorLevelQReal.lean:361), so `cb 2 5 = 25/21`.

HONEST STATUS: this shows ONLY that the real-number inequalities are jointly satisfiable at one
parameter point (they are not vacuous as arithmetic).  NO `CongruentDissection` / `HFrame` /
`L3S` exists here; the geometric hypotheses (`hS`, `L : LFrame F`) are NOT witnessed.
-/

namespace Erdos634.Draft.FDFDepthWitness

open Erdos634.Draft.RowWallReal

theorem cb_2_5 : cb 2 5 = 25 / 21 := by
  unfold cb; norm_num

/-- `hkL` of `l3m_band`/`l3m_terminal`. -/
theorem hkL_wit : (0 : ℕ) + 1 ≤ 3 := by norm_num

/-- `L' = k' + 1 + w0`. -/
theorem hw0_wit : (3 : ℕ) = 0 + 1 + 2 := by norm_num

/-- `hWlt` as in `l3m_band` (W_L interior): `(w0+1) + (k'+1) cb < f`. -/
theorem hWlt_wit :
    (((2 : ℕ) : ℝ) + 1) + (((0 : ℕ) : ℝ) + 1) * cb 2 5 < ((5 : ℕ) : ℝ) := by
  rw [cb_2_5]; norm_num

/-- `hexit` of `l3m_terminal`, verbatim shape. -/
theorem hexit_wit :
    ((5 : ℕ) : ℝ) < (((3 : ℕ) : ℝ) - ((0 : ℕ) : ℝ) + 1) + (((0 : ℕ) : ℝ) + 1) * cb 2 5 := by
  rw [cb_2_5]; norm_num

/-- `L = L' + 1 = 4 < f = 5`. -/
theorem L_lt_f_wit : (3 : ℕ) + 1 < 5 := by norm_num

end Erdos634.Draft.FDFDepthWitness
