/-
Finite instances of Lemma S' (R = R_0) for 5-smooth n with 15 | n, by the Corollary-F certificate checker
(`LemmaS.allCert`, `decide +kernel`, no `native_decide`).  Each `allCert_n` gives, via `LemmaS.of_allCert`, `relSpace n a = trivSpace n a`
for every primitive tile of that n, hence (with `r0c_core15`, `lemmaH15_holds`) the n-instance of GapA2.
These are single values of n; they do not close any infinite family.
The checker rejects n = 30 and n = 60 (Lemma S' fails there): `allCert_30_false`, `allCert_60_false`.
-/
import Mathlib
import Erdos634.Draft.GA2OBase
import Erdos634.Draft.GA2OC30
import Erdos634.Draft.GA2OC60
import Erdos634.Draft.GA2OC45
import Erdos634.Draft.GA2OC75
import Erdos634.Draft.GA2OC90

namespace Erdos634.GA2OFin

open Erdos634.LemmaS

theorem allCert_30_false : allCert 30 = false := Erdos634.GA2OC.cert_30
theorem allCert_60_false : allCert 60 = false := Erdos634.GA2OC.cert_60
theorem allCert_45 : allCert 45 = true := Erdos634.GA2OC.cert_45
theorem allCert_75 : allCert 75 = true := Erdos634.GA2OC.cert_75
theorem allCert_90 : allCert 90 = true := Erdos634.GA2OC.cert_90

end Erdos634.GA2OFin

#print axioms Erdos634.GA2OFin.allCert_30_false
#print axioms Erdos634.GA2OFin.allCert_60_false
#print axioms Erdos634.GA2OFin.allCert_45
#print axioms Erdos634.GA2OFin.allCert_75
#print axioms Erdos634.GA2OFin.allCert_90
