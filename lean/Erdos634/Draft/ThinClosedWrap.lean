import Erdos634.ThinClosed

namespace Erdos634.Draft.ThinClosedWrap
open Erdos634.ThinClosed

theorem wrap_thin_no_tiling (tiling : Prop) (bp cp : ℕ) (hne : bp ≠ cp)
    (cascade_west : bp < cp → tiling → False)
    (cascade_east : cp < bp → tiling → False)
    (h : tiling) : False :=
  thin_no_tiling tiling bp cp hne cascade_west cascade_east h

example : True := trivial
#print axioms wrap_thin_no_tiling

end Erdos634.Draft.ThinClosedWrap
