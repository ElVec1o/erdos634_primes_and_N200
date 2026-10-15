import Erdos634.R126CBridge

namespace Erdos634.Draft.R126CBridgeWrap
open Erdos634.R126CBridge

theorem wrap_r126_nonempty_congruentDissection :
    Nonempty (Erdos634.Geometry.CongruentDissection 126) :=
  r126_nonempty_congruentDissection

example : True := trivial
#print axioms wrap_r126_nonempty_congruentDissection

end Erdos634.Draft.R126CBridgeWrap
