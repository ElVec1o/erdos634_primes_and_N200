import Erdos634.SssCongruent

namespace Erdos634.Draft.SssCongruentWrap
open Erdos634.SssCongruent Erdos634.Geometry RealInnerProductSpace

theorem wrap_congruent_of_sq_dist_perm {T U : Tri} (σ : Equiv.Perm (Fin 3))
    (hd : ∀ i j, dist (T.pts i) (T.pts j) ^ 2 = dist (U.pts (σ i)) (U.pts (σ j)) ^ 2) :
    T.Congruent U :=
  congruent_of_sq_dist_perm σ hd

example : True := trivial
#check @wrap_congruent_of_sq_dist_perm

end Erdos634.Draft.SssCongruentWrap
