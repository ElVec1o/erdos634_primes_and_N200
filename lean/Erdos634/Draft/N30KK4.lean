/-
N30K-K4 (split of the controls to stay under 9 GB): controls for the constant-30 checker (the same `chkTileF` / table `slc c`, `shc c` as the real kill).
`GA2RK.control_reports` already shows: with the constant replaced by fac = 1, 4, 9 the checker REPORTS solutions (Bool false) on all ten
S'-exceptional tiles.  Here the same is shown on the ALL-TILES driver `chkAllXF` (the object used in `chk30F`/`chk60F`): the first-entry slice of the
tile (24,5,1) at n = 30 resp. (49,10,1) at n = 60 is FALSE for fac = 1, 4, 9, hence `chkAllF fac = true` is refuted for those constants, so `chk30F`/`chk60F`
are not vacuous consequences of the shape of the driver; and `chkTileF_thirty_ten` (constant 30, ten tiles, the same table) is true.
No sorry / native_decide.
-/
import Mathlib
import Erdos634.Draft.N30KC
import Erdos634.Draft.GA2RK

namespace Erdos634.N30K

open Erdos634.GA2R

theorem control_driver_reports_4 :
    chkAllXF 4 (slc 2) (shc 2) 30 24 = false ∧ chkAllXF 4 (slc 1) (shc 1) 60 49 = false := by
  decide +kernel

theorem control_chkAllF_false_4 :
    chkAllF 4 (slc 2) (shc 2) 30 = false ∧ chkAllF 4 (slc 1) (shc 1) 60 = false := by
  obtain ⟨h1, h2⟩ := control_driver_reports_4
  constructor
  · unfold chkAllF
    rw [List.all_eq_false]
    exact ⟨24, List.mem_range.mpr (by norm_num), by simp [h1]⟩
  · unfold chkAllF
    rw [List.all_eq_false]
    exact ⟨49, List.mem_range.mpr (by norm_num), by simp [h2]⟩

#print axioms control_chkAllF_false_4

end Erdos634.N30K
