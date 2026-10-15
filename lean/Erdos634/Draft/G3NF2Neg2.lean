-- Draft/G3NF2Neg2.lean — Rejection checks for the chunked F2 certificate (small, hand-written):
-- (i) a target with one vertex (the origin corner, moved by 1000 lattice units) is rejected by the containment test used by Cert.ok on the real clusters 3 and 4;
-- (ii) the model with one vertex moved is rejected by the congruence test on the real clusters 3 and 4;
-- (iii) the real cluster 3 and the real cluster 4 are not separated by an unrelated line.
import Erdos634.Draft.G3NF2Cl3
import Erdos634.Draft.G3NF2Cl4
import Erdos634.Draft.G3NF2Data
namespace Erdos634.Draft.G3NF2Neg2
open Erdos634.Draft.G3CCert
open Erdos634.Draft.G3NF2Cl3 (cl3)
open Erdos634.Draft.G3NF2Cl4 (cl4)

def badTarget : LT := ((1000,0),(15015,-6825),(18865,8575))
def badModel : LT := ((0,0),(294,0),(539,246))

theorem bad_target3 : cl3.leaves.all (insideT badTarget) = false := by decide +kernel
theorem bad_target4 : cl4.leaves.all (insideT badTarget) = false := by decide +kernel
theorem bad_model3 : cl3.leaves.all (congT badModel) = false := by decide +kernel
theorem bad_model4 : cl4.leaves.all (congT badModel) = false := by decide +kernel
theorem bad_sep : clSep (0,0) (294,0) cl3 cl4 = false := by decide +kernel

-- positive counterpart of the same predicates on the true data (must hold)
theorem good_target3 : cl3.leaves.all (insideT Erdos634.Draft.G3NF2Data.target) = true := by decide +kernel
theorem good_model3 : cl3.leaves.all (congT Erdos634.Draft.G3NF2Data.model) = true := by decide +kernel

end Erdos634.Draft.G3NF2Neg2
