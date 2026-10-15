/- Chunk of the GA2OC certificate: rows a0 in [40, 50) of allCert 75 (single `decide +kernel`). -/
import Mathlib
import Erdos634.Draft.GA2OCDefs

namespace Erdos634.GA2OC

theorem rows_75e : rowsOK 75 40 10 = true := by decide +kernel

end Erdos634.GA2OC

#print axioms Erdos634.GA2OC.rows_75e
