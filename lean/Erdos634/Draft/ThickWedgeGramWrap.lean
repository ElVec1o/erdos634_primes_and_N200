import Erdos634.ThickWedgeGram

namespace Erdos634.Draft.ThickWedgeGramWrap
open Erdos634.ThickWedgeGram
open Erdos634.ThickJunctionCoords Erdos634.MarchInduction

theorem wrap_wedge_extremal_coords63_nonvacuous :
    p63 * apexH63 ≤ apexH63 * p63 ∧ apexH63 * p63 ≤ q63 * apexH63 ∧
    p63 * apexH63 ≤ apexH63 * q63 ∧ apexH63 * q63 ≤ q63 * apexH63 ∧
    p63 ^ 2 + apexH63 ^ 2 = b63 ^ 2 ∧ q63 ^ 2 + apexH63 ^ 2 = c63 ^ 2 ∧
    (p63 - q63) ^ 2 + (apexH63 - apexH63) ^ 2 = a63 ^ 2 :=
  wedge_extremal_coords63_nonvacuous

example : True := trivial
#print axioms wrap_wedge_extremal_coords63_nonvacuous

end Erdos634.Draft.ThickWedgeGramWrap
