import Erdos634.ElevenMBridge

namespace Erdos634.Draft.ElevenMBridgeWrap
open Erdos634.ElevenMBridge Erdos634.Geometry

theorem wrap_exists_dissection_11_mul_sq {m : ℕ} (hm : 0 < m) (h : 2 ∣ m ∨ 3 ∣ m) :
    ∃ N, N = 11 * m ^ 2 ∧ Nonempty (CongruentDissection N) :=
  exists_dissection_11_mul_sq hm h

example : True := trivial
#print axioms wrap_exists_dissection_11_mul_sq

end Erdos634.Draft.ElevenMBridgeWrap
