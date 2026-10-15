import Erdos634.EqSpecAlgebra

namespace Erdos634.Draft.EqSpecAlgebraWrap
open Erdos634.EqSpecAlgebra

-- disc_eq uses `variable {a b c S : ℝ}`, so they are implicit in the source.
-- We wrap converse_triple which has no such implicit variables.
theorem wrap_converse_triple (u v q : ℝ) (h : q ^ 2 = (v - u) ^ 2 + 16 * (u * v / 3)) :
    (2 * (u + v)) ^ 2 = (q + (v - u)) ^ 2 + (q + (v - u)) * (q - (v - u)) + (q - (v - u)) ^ 2 :=
  converse_triple u v q h

example : True := trivial
#print axioms wrap_converse_triple

end Erdos634.Draft.EqSpecAlgebraWrap
