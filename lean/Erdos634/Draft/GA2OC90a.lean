/- Chunk of the GA2OC certificate: rows a0 in [0, 10) of allCert 90 (single `decide +kernel`). -/
import Mathlib
import Erdos634.Draft.GA2OCDefs

namespace Erdos634.GA2OC

theorem rows_90a : rowsOK 90 0 10 = true := by decide +kernel

end Erdos634.GA2OC

#print axioms Erdos634.GA2OC.rows_90a
