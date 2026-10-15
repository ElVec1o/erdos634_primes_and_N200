import Erdos634.CornerAnglePermTarget

namespace Erdos634.Draft.CornerAnglePermTargetWrap
open Erdos634.Geometry

theorem wrap_cornerAngle_sum_indexed (T : Tri) (a : Fin 3) :
    cornerAngle (T.pts (a + 1)) (T.pts a) (T.pts (a + 2))
      + cornerAngle (T.pts (a + 1 + 1)) (T.pts (a + 1)) (T.pts (a + 1 + 2))
      + cornerAngle (T.pts (a + 2 + 1)) (T.pts (a + 2)) (T.pts (a + 2 + 2)) = Real.pi :=
  cornerAngle_sum_indexed T a

theorem wrap_htarget_of_isosceles (T : Tri) {α β : ℝ} (hrel : 3 * α + 2 * β = Real.pi) (a : Fin 3)
    (h₁ : cornerAngle (T.pts (a + 1 + 1)) (T.pts (a + 1)) (T.pts (a + 1 + 2)) = β)
    (h₂ : cornerAngle (T.pts (a + 2 + 1)) (T.pts (a + 2)) (T.pts (a + 2 + 2)) = β) :
    ∀ k : Fin 3, cornerAngle (T.pts (k + 1)) (T.pts k) (T.pts (k + 2)) = 3 * α ∨
      cornerAngle (T.pts (k + 1)) (T.pts k) (T.pts (k + 2)) = β :=
  htarget_of_isosceles T hrel a h₁ h₂

theorem wrap_third_corner_of_base_apex (T : Tri) {α β : ℝ} (hrel : 3 * α + 2 * β = Real.pi) (k : Fin 3)
    (hbase : cornerAngle (T.pts (k + 1)) (T.pts k) (T.pts (k + 2)) = β)
    (hapex : cornerAngle (T.pts (k + 1 + 1)) (T.pts (k + 1)) (T.pts (k + 1 + 2)) = 3 * α) :
    cornerAngle (T.pts (k + 2 + 1)) (T.pts (k + 2)) (T.pts (k + 2 + 2)) = β :=
  third_corner_of_base_apex T hrel k hbase hapex

example : True := trivial
#print axioms wrap_cornerAngle_sum_indexed

end Erdos634.Draft.CornerAnglePermTargetWrap
