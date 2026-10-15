/- GA2OC: allCert 90 = true, assembled from the six row chunks GA2OC90a..f. -/
import Mathlib
import Erdos634.Draft.GA2OCDefs
import Erdos634.Draft.GA2OC90a
import Erdos634.Draft.GA2OC90b
import Erdos634.Draft.GA2OC90c
import Erdos634.Draft.GA2OC90d
import Erdos634.Draft.GA2OC90e
import Erdos634.Draft.GA2OC90f

namespace Erdos634.GA2OC

theorem cert_90 : Erdos634.LemmaS.allCert 90 = true := by
  have h1 : rowsOK 90 0 10 = true := rows_90a
  have h2 : rowsOK 90 0 20 = true := by
    have := rowsOK_add 90 0 10 10 h1 (by simpa using rows_90b)
    simpa using this
  have h3 : rowsOK 90 0 30 = true := by
    have := rowsOK_add 90 0 20 10 h2 (by simpa using rows_90c)
    simpa using this
  have h4 : rowsOK 90 0 45 = true := by
    have := rowsOK_add 90 0 30 15 h3 (by simpa using rows_90d)
    simpa using this
  have h5 : rowsOK 90 0 60 = true := by
    have := rowsOK_add 90 0 45 15 h4 (by simpa using rows_90e)
    simpa using this
  have h6 : rowsOK 90 0 90 = true := by
    have := rowsOK_add 90 0 60 30 h5 (by simpa using rows_90f)
    simpa using this
  exact allCert_of_rows_all 90 h6

end Erdos634.GA2OC

#print axioms Erdos634.GA2OC.cert_90
