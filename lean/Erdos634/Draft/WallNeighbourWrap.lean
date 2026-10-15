import Erdos634.WallNeighbour

namespace Erdos634.Draft.WallNeighbourWrap
open Erdos634.WallNeighbour

theorem wrap_seven_eleven_covered : (11:ℤ) ^ 4 - 3 * 7 ^ 2 * 11 ^ 2 + 7 ^ 4 < 0 :=
  seven_eleven_covered

example : True := trivial
#check @wrap_seven_eleven_covered

end Erdos634.Draft.WallNeighbourWrap
