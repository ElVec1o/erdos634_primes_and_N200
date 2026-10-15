import Erdos634.RunForcing

namespace Erdos634.Draft.RunForcingWrap
open Erdos634.RunForcing

theorem wrap_march_cannot_reach_essential {k f : ℤ} (hforced : k < f) (hessential : f ≤ k) :
    False :=
  march_cannot_reach_essential hforced hessential

example : True := trivial
#print axioms wrap_march_cannot_reach_essential

end Erdos634.Draft.RunForcingWrap
