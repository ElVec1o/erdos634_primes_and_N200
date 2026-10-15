import Erdos634.SectorArea

namespace Erdos634.Draft.SectorAreaWrap
open Erdos634.SectorArea

theorem wrap_volume_sector {θ : ℝ} (hθ : 0 ≤ θ) (hθ' : θ < Real.pi) :
    MeasureTheory.volume (sector θ) = ENNReal.ofReal (θ / 2) :=
  volume_sector hθ hθ'

example : True := trivial
#print axioms wrap_volume_sector

end Erdos634.Draft.SectorAreaWrap
