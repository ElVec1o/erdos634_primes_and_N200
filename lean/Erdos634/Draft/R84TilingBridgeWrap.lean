import Erdos634.R84TilingBridge

namespace Erdos634.Draft.R84TilingBridgeWrap
open Erdos634.R84TilingBridge

theorem wrap_r84_nonempty_congruentDissection :
    Nonempty (Erdos634.Geometry.CongruentDissection 84) :=
  r84_nonempty_congruentDissection

example : True := trivial
#print axioms wrap_r84_nonempty_congruentDissection

end Erdos634.Draft.R84TilingBridgeWrap
