import Erdos634.W2Core

namespace Erdos634.Draft.W2CoreWrap
open Erdos634.W2Core

theorem wrap_sum_forcing_f12 (j s : Int) (hj : 0 ≤ j) (hjf : j < 12)
    (hs : -j ≤ s) (hs2 : s ≤ j) (hd : (24 : Int) ∣ (s - j)) : s = j :=
  sum_forcing_f12 j s hj hjf hs hs2 hd

example : True := trivial
#print axioms wrap_sum_forcing_f12

end Erdos634.Draft.W2CoreWrap
