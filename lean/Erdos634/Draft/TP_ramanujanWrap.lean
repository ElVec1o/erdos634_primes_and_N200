import Erdos634.TP_ramanujan

namespace Erdos634.Draft.TP_ramanujanWrap
open Erdos634.TPRamanujan

theorem wrap_witness_real_neg : ¬ ((0 : ℝ) ≤ 3 - Real.sqrt 15) :=
  witness_real_neg

example : True := trivial
#check @witness_real_neg

end Erdos634.Draft.TP_ramanujanWrap
