import Erdos634.ThinFamily

namespace Erdos634.Draft.ThinFamilyWrap
open Erdos634.ThinFamily

theorem wrap_thin_word_spans (f : ℤ) :
    0 * (1 * f) + 1 * (f ^ 2 - 1 ^ 2) + 2 * f ^ 2 = 1 * (3 * f ^ 2 - 1 ^ 2) :=
  thin_word_spans f

example : True := trivial
#print axioms wrap_thin_word_spans

end Erdos634.Draft.ThinFamilyWrap
