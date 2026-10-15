import Erdos634.TargetShapeDissection

namespace Erdos634.Draft.TargetShapeDissectionWrap
open Erdos634.TargetShapeDissection
open Erdos634.Geometry Erdos634.TargetShape

theorem wrap_congruentDissection_target_shape {N : ℕ} (D : CongruentDissection N) (e f β : ℝ)
    (he : 0 < e) (hef : e < f) (a : Fin 3)
    (p q r : Plane)
    (hpq : dist p q = e * f) (hrq : dist r q = f ^ 2) (hpr : dist p r = f ^ 2 - e ^ 2)
    (hβ : cornerAngle p q r = β)
    (h₁ : cornerAngle (D.target.pts (a + 1 + 1)) (D.target.pts (a + 1)) (D.target.pts (a + 1 + 2)) = β)
    (h₂ : cornerAngle (D.target.pts (a + 2 + 1)) (D.target.pts (a + 2)) (D.target.pts (a + 2 + 2)) = β)
    (hsin : Real.sin (cornerAngle (D.target.pts (a + 1)) (D.target.pts a) (D.target.pts (a + 2))) ≠ 0)
    (hAB0 : 0 < dist (D.target.pts a) (D.target.pts (a + 1)))
    (hBC0 : dist (D.target.pts (a + 1)) (D.target.pts (a + 2)) ≠ 0) :
    ∃ k : ℝ, 0 < k ∧
      dist (D.target.pts a) (D.target.pts (a + 1)) = k * f ^ 3 ∧
      dist (D.target.pts a) (D.target.pts (a + 2)) = k * f ^ 3 ∧
      dist (D.target.pts (a + 1)) (D.target.pts (a + 2)) = k * e * (3 * f ^ 2 - e ^ 2) :=
  congruentDissection_target_shape D e f β he hef a p q r hpq hrq hpr hβ h₁ h₂ hsin hAB0 hBC0

example : True := trivial
#check @wrap_congruentDissection_target_shape

end Erdos634.Draft.TargetShapeDissectionWrap
