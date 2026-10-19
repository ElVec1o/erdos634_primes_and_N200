-- Draft/ThmWLib2.lean — generic area bookkeeping for a packing into a skew-frame triangle.  UNAUDITED.  No sorry.
import Erdos634.Draft.LadderFam
open scoped Classical
open Erdos634.Geometry
namespace Erdos634.Draft.ThmW
open Erdos634.Draft.WFrameF Erdos634.Draft.WBrickF
open Erdos634.Draft.S2L (vol_triC)

open MeasureTheory in
/-- `n` model bricks have the area of the skew triangle `tA tB tC` when `n · (A B) = cross`. -/
theorem hvol_gen {F : ℝ} (hF : 1 < F) (A B : ℝ) (hA : 0 < A) (hB : 0 < B) (tA tB tC : ℝ × ℝ)
    (h : (tB.1 - tA.1) * (tC.2 - tA.2) - (tC.1 - tA.1) * (tB.2 - tA.2) ≠ 0) (n : ℕ)
    (hc : (n : ℝ) * (A * B) = (tB.1 - tA.1) * (tC.2 - tA.2) - (tC.1 - tA.1) * (tB.2 - tA.2)) :
    (n : ENNReal) * volume (brickL F hF A B hA hB).carrier = volume (triC F hF tA tB tC h).carrier := by
  have hs := sD_pos hF
  have hF0 : 0 < F := by linarith
  have hM : volume (brickL F hF A B hA hB).carrier = ENNReal.ofReal (sD F / (2 * F) * (A * B)) * volume Erdos634.AreaDet.stdCarrier := by
    unfold brickL
    rw [vol_triC]
    congr 2
    rw [← abs_of_pos (show 0 < sD F / (2 * F) * (A * B) by positivity)]
    congr 1; ring
  have hcn : 0 ≤ (tB.1 - tA.1) * (tC.2 - tA.2) - (tC.1 - tA.1) * (tB.2 - tA.2) := by
    rw [← hc]; positivity
  have hT : volume (triC F hF tA tB tC h).carrier = ENNReal.ofReal (sD F / (2 * F) * ((tB.1 - tA.1) * (tC.2 - tA.2) - (tC.1 - tA.1) * (tB.2 - tA.2)))
      * volume Erdos634.AreaDet.stdCarrier := by
    rw [vol_triC]
    congr 2
    exact abs_of_nonneg (by positivity)
  rw [hM, hT, ← mul_assoc, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  congr 2
  rw [← hc]; ring

end Erdos634.Draft.ThmW

