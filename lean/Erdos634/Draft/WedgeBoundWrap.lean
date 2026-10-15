import Erdos634.WedgeBound

namespace Erdos634.Draft.WedgeBoundWrap
open Erdos634.Wedge

theorem wrap_east_block_ge_four (e : ℤ) (he : 2 ≤ e) : 4 ≤ e^2 :=
  east_block_ge_four e he

example : True := trivial
#check @wrap_east_block_ge_four

end Erdos634.Draft.WedgeBoundWrap
