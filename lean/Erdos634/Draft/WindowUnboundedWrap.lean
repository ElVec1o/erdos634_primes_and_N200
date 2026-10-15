import Erdos634.WindowUnbounded

namespace Erdos634.Draft.WindowUnboundedWrap
open Erdos634.WindowUnbounded

theorem wrap_no_scale_invariant_bound (width : ℕ → ℕ) (hw : ∀ n, width n = 2 * n + 7)
    (K : ℕ) (hinv : ∀ n, width n ≤ K) : False :=
  no_scale_invariant_bound width hw K hinv

example : True := trivial
#check @wrap_no_scale_invariant_bound

end Erdos634.Draft.WindowUnboundedWrap
