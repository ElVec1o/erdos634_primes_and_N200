import Erdos634.UniformFill

namespace Erdos634.Draft.UniformFillWrap
open Erdos634.UniformFill

theorem wrap_base_is_three_spans (f : ℕ) : 3 * f ^ 2 - 1 = 3 * (f ^ 2) - 1 :=
  base_is_three_spans f

example : True := trivial
#print axioms wrap_base_is_three_spans

end Erdos634.Draft.UniformFillWrap
