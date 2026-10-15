import Erdos634.WbtwMinimalPrecedesRest

namespace Erdos634.Draft.WbtwMinimalPrecedesRestWrap
open Erdos634.ChordTraceReal Erdos634.Geometry

theorem wrap_far_precedes_of_minimal {p q r s rk sk : Plane}
    (hr : Wbtw ℝ p r q) (hs : Wbtw ℝ p s q) (hrk : Wbtw ℝ p rk q) (hsk : Wbtw ℝ p sk q)
    (hrs : r ≠ s) (hrksk : rk ≠ sk)
    (ho : Wbtw ℝ p r s) (hok : Wbtw ℝ p rk sk)
    (hdisj : (segment ℝ r s ∩ segment ℝ rk sk).Subsingleton)
    (hmin : Wbtw ℝ p r rk) :
    Wbtw ℝ p s rk :=
  far_precedes_of_minimal hr hs hrk hsk hrs hrksk ho hok hdisj hmin

example : True := trivial
#check @wrap_far_precedes_of_minimal

end Erdos634.Draft.WbtwMinimalPrecedesRestWrap
