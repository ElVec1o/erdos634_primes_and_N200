import Erdos634.RogueMirror

namespace Erdos634.Draft.RogueMirrorWrap
open Erdos634.RogueMirror

theorem wrap_wall_base_reading (e f b na nb nc P Q R : ℕ) (he : 1 ≤ e)
    (hef : e < f) (hcop : Nat.Coprime e f) (hb : b + e ^ 2 = f ^ 2)
    (heq : na * (e * f) + nb * b + nc * f ^ 2 = f * b)
    (hcside : P * (e * f) + Q * b + R * (f * f) = f * f * f)
    (hgamma : 1 ≤ R) (hflank : 1 ≤ nb ∨ 1 ≤ Q) :
    na = 0 ∧ nb = f ∧ nc = 0 :=
  wall_base_reading e f b na nb nc P Q R he hef hcop hb heq hcside hgamma hflank

example : True := trivial
#print axioms wrap_wall_base_reading

end Erdos634.Draft.RogueMirrorWrap
