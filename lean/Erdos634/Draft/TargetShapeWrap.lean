import Erdos634.TargetShape

namespace Erdos634.Draft.TargetShapeWrap
open Erdos634.TargetShape
open Erdos634.Geometry Erdos634.AngleThreshold Erdos634.CevianRealization

theorem wrap_target_shape (A B C : Plane) (e f : ℝ) (he : 0 < e) (hef : e < f)
    (β : ℝ) (p q r : Plane)
    (hpq : dist p q = e * f) (hrq : dist r q = f ^ 2) (hpr : dist p r = f ^ 2 - e ^ 2)
    (hβ : cornerAngle p q r = β)
    (hB : cornerAngle A B C = β) (hC : cornerAngle A C B = β)
    (hsin : Real.sin (cornerAngle B A C) ≠ 0) (hAB0 : 0 < dist A B)
    (hBC0 : dist B C ≠ 0) :
    ∃ k : ℝ, 0 < k ∧
      dist A B = k * f ^ 3 ∧ dist A C = k * f ^ 3 ∧ dist B C = k * e * (3 * f ^ 2 - e ^ 2) :=
  target_shape A B C e f he hef β p q r hpq hrq hpr hβ hB hC hsin hAB0 hBC0

example : True := trivial
#check @wrap_target_shape

end Erdos634.Draft.TargetShapeWrap
