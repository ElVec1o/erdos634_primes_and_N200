import Erdos634.ThickAngleIrrational

namespace Erdos634.Draft.ThickAngleIrrationalWrap
open Erdos634.ThickAngleIrrational
open Erdos634.BaseBetaTargetCoord Erdos634.ThickJunctionCoords

theorem wrap_modelAlpha_irrational_23 : ¬ ∃ r : ℚ, modelAlpha 2 3 = (r : ℝ) * Real.pi :=
  modelAlpha_irrational_23

example : True := trivial
#print axioms wrap_modelAlpha_irrational_23

end Erdos634.Draft.ThickAngleIrrationalWrap
