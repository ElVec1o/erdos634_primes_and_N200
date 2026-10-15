import Erdos634.TransverseChain

namespace Erdos634.Draft.TransverseChainWrap
open Erdos634.TransverseChain

theorem wrap_phit_not_breakpoint (e f b s : ℕ)
    (hcop : Nat.Coprime e f) (hb : b + e ^ 2 = f ^ 2)
    (hs1 : 1 ≤ s) (hsf : s < f) (hdvd : f ∣ s * e * b) : False :=
  phit_not_breakpoint e f b s hcop hb hs1 hsf hdvd

example : True := trivial
#print axioms wrap_phit_not_breakpoint

end Erdos634.Draft.TransverseChainWrap
