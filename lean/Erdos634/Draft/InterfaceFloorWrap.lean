import Erdos634.InterfaceFloor

namespace Erdos634.Draft.InterfaceFloorWrap

open Erdos634.InterfaceFloor

theorem if_interface_floor (e f na nb nc : ℤ) (he : 0 < e) (hef : e < f)
    (hc : IsCoprime f e)
    (hrel : na * (e * f) + nb * (f ^ 2 - e ^ 2) + nc * f ^ 2 = 0)
    (hne : ¬ (na = 0 ∧ nb = 0 ∧ nc = 0)) :
    f * min (e * f) (f ^ 2 - e ^ 2)
      ≤ oneSided na nb nc (e * f) (f ^ 2 - e ^ 2) (f ^ 2) :=
  interface_floor e f na nb nc he hef hc hrel hne

theorem if_floor_attained (e f : ℤ) (he : 0 < e) (hf : 0 < f) :
    oneSided f 0 (-e) (e * f) (f ^ 2 - e ^ 2) (f ^ 2) = f * (e * f) :=
  floor_attained e f he hf

example : True := trivial

#print axioms if_interface_floor
#print axioms if_floor_attained

end Erdos634.Draft.InterfaceFloorWrap
