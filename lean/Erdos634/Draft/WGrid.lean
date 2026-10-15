-- Draft/WGrid.lean — step (c) of the 7m² plan: the W-parallelogram of size (6(k+1)) × (7(l+1)),
-- a grid of 14(k+1)(l+1) tiles from translates of the unit 6×7 parallelogram.
import Erdos634.Draft.WPgram

open scoped Classical
open Erdos634.Geometry Erdos634.CertCoord
open Erdos634.Draft.CollarParam (s15 s15_pos s15_sq Sh Tset Rect RTiling.cast RTiling.castN)

namespace Erdos634.Draft.WGrid
open Erdos634.Draft.WFrame Erdos634.Draft.RegionTiling Erdos634.Draft.WBrick Erdos634.Draft.WPgram

/-- A horizontal strip of `k+1` unit parallelograms. -/
noncomputable def strip : (k : ℕ) → RTiling (Phi '' Rect 0 (6 * ((k : ℝ) + 1)) 0 7) MW (14 * (k + 1))
  | 0 => by
      refine RTiling.cast (by norm_num) (RTiling.castN (by norm_num) pgram6x7)
  | k + 1 => by
      have s := shift_rect pgram6x7 (6 * ((k : ℝ) + 1)) 0 (6 * (((k + 1 : ℕ) : ℝ) + 1)) 7
        (by push_cast; ring) (by norm_num)
      have h := hstack (by positivity) (by push_cast; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]) (strip k) s
      exact RTiling.castN (by ring) h

/-- **Step (c).** The grid: `(k+1) × (l+1)` unit parallelograms. -/
noncomputable def grid (k : ℕ) : (l : ℕ) →
    RTiling (Phi '' Rect 0 (6 * ((k : ℝ) + 1)) 0 (7 * ((l : ℝ) + 1))) MW (14 * (k + 1) * (l + 1))
  | 0 => by
      refine RTiling.cast (by norm_num) (RTiling.castN (by ring) (strip k))
  | l + 1 => by
      have s := shift_rect (strip k) 0 (7 * ((l : ℝ) + 1)) (6 * ((k : ℝ) + 1) + 0)
        (7 * (((l + 1 : ℕ) : ℝ) + 1)) (by ring) (by push_cast; ring)
      simp only [add_zero] at s
      have h := vstack (by positivity) (by push_cast; linarith [(Nat.cast_nonneg l : (0 : ℝ) ≤ l)])
        (grid k l) s
      exact RTiling.castN (by ring) h

end Erdos634.Draft.WGrid

#print axioms Erdos634.Draft.WGrid.grid
