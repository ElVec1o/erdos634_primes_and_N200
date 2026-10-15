/- Chunk of the GA2OC certificate: the single `decide +kernel` check allCert 60 = false (re-chunk of GA2OFin). -/
import Mathlib
import Erdos634.Draft.GA2OBase

namespace Erdos634.GA2OC

open Erdos634.LemmaS

theorem cert_60 : allCert 60 = false := by decide +kernel

end Erdos634.GA2OC

#print axioms Erdos634.GA2OC.cert_60
