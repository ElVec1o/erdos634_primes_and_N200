import Erdos634.WallStraddle

namespace Erdos634.Draft.WallStraddleWrap
open Erdos634.WallStraddle

theorem wrap_middle_even (e f : ℤ) : ∃ k : ℤ, 2 * (f ^ 2 - e ^ 2) = 2 * k :=
  middle_even e f

example : True := trivial
#check @wrap_middle_even

end Erdos634.Draft.WallStraddleWrap
