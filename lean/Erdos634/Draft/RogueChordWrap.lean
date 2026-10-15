import Erdos634.RogueChord

namespace Erdos634.Draft.RogueChordWrap
open Erdos634.RogueChord

theorem wrap_swap_fits (e f M : ℤ) (he : 0 < e) (hef : e < f) (hM : e + f < M * e) :
    e * f + f ^ 2 < M * (e * f) ∧ e * f ≠ f ^ 2 :=
  swap_fits e f M he hef hM

example : True := trivial
#print axioms wrap_swap_fits

end Erdos634.Draft.RogueChordWrap
