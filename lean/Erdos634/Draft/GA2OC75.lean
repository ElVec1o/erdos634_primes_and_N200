/- GA2OC: allCert 75 = true, assembled from the six row chunks GA2OC75a..f. -/
import Mathlib
import Erdos634.Draft.GA2OCDefs
import Erdos634.Draft.GA2OC75a
import Erdos634.Draft.GA2OC75b
import Erdos634.Draft.GA2OC75c
import Erdos634.Draft.GA2OC75d
import Erdos634.Draft.GA2OC75e
import Erdos634.Draft.GA2OC75f

namespace Erdos634.GA2OC

theorem cert_75 : Erdos634.LemmaS.allCert 75 = true := by
  have h1 : rowsOK 75 0 10 = true := rows_75a
  have h2 : rowsOK 75 0 20 = true := by
    have := rowsOK_add 75 0 10 10 h1 (by simpa using rows_75b)
    simpa using this
  have h3 : rowsOK 75 0 30 = true := by
    have := rowsOK_add 75 0 20 10 h2 (by simpa using rows_75c)
    simpa using this
  have h4 : rowsOK 75 0 40 = true := by
    have := rowsOK_add 75 0 30 10 h3 (by simpa using rows_75d)
    simpa using this
  have h5 : rowsOK 75 0 50 = true := by
    have := rowsOK_add 75 0 40 10 h4 (by simpa using rows_75e)
    simpa using this
  have h6 : rowsOK 75 0 75 = true := by
    have := rowsOK_add 75 0 50 25 h5 (by simpa using rows_75f)
    simpa using this
  exact allCert_of_rows_all 75 h6

end Erdos634.GA2OC

#print axioms Erdos634.GA2OC.cert_75
