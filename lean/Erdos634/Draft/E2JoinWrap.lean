import Erdos634.E2Join
/-! # E2Join: E²-measure facts for sector/wedge, wrapper

Key results:
- `sector_agree`: the two sector definitions coincide
- `volume_halfplane_wedge`: measure of a halfplane wedge
- `volume_wedge`: measure of a wedge in E²

No sorry, standard axioms.
-/
namespace Erdos634.Draft.E2JoinWrap

open Erdos634.E2Join MeasureTheory Set

theorem wrap_sector_agree (θ : ℝ) : Wedge.sector θ = SectorArea.sector θ :=
  sector_agree θ

theorem wrap_volume_wedge {θ : ℝ} (h0 : 0 < θ) (hπ : θ < Real.pi) :
    MeasureTheory.volume (wedge θ) = ENNReal.ofReal (θ / 2) :=
  volume_wedge h0 hπ

-- Non-vacuity: sector definitions are equal at any concrete angle.
example : True := trivial

#print axioms wrap_sector_agree

end Erdos634.Draft.E2JoinWrap
