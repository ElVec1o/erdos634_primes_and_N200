import Erdos634.OverlapAsymmetry

namespace Erdos634.Draft.OverlapAsymmetryWrap
open Erdos634.OverlapAsymmetry

theorem wrap_sym_of_step_and_frame_base (u : ℕ → Bool)
    (step : ∀ j, u j = true → u (j + 1) = true) (base : u 0 = true) :
    ∀ j, u j = true :=
  sym_of_step_and_frame_base u step base

example : True := trivial
#print axioms wrap_sym_of_step_and_frame_base

end Erdos634.Draft.OverlapAsymmetryWrap
