import Erdos634.VacCheck

namespace Erdos634.Draft.VacCheckWrap
open Erdos634.RouteOne Erdos634.Geometry

theorem wrap_approachWitness_sat (n : ℕ) :
    0 < (approachWitness n - (0 : Plane)) 0 ∧
    (approachWitness n - (0 : Plane)) 1
      ≤ (1 / (n + 1 : ℝ)) * ((approachWitness n - (0 : Plane)) 0) ∧
    0 < (approachWitness n - (0 : Plane)) 1 ∧
    dist (approachWitness n) (0 : Plane) < 2 / (n + 1 : ℝ) :=
  approachWitness_sat n

example : True := trivial
#print axioms wrap_approachWitness_sat

end Erdos634.Draft.VacCheckWrap
