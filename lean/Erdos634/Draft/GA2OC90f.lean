/- Chunk of the GA2OC certificate: rows a0 in [60, 90) of allCert 90 (single `decide +kernel`). -/
import Mathlib
import Erdos634.Draft.GA2OCDefs

namespace Erdos634.GA2OC

theorem rows_90f : rowsOK 90 60 30 = true := by decide +kernel

end Erdos634.GA2OC

#print axioms Erdos634.GA2OC.rows_90f
