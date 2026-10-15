import Erdos634.Wedge

namespace Erdos634.Draft.WedgeWrap
open Erdos634.Wedge

theorem wrap_sector_eq_halfplanes {θ : ℝ} (h0 : 0 < θ) (hπ : θ < Real.pi) :
    sector θ = {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 < 1}
             ∩ {p : ℝ × ℝ | 0 < p.2}
             ∩ {p : ℝ × ℝ | 0 < Real.sin θ * p.1 - Real.cos θ * p.2} :=
  sector_eq_halfplanes h0 hπ

example : True := trivial
#check @wrap_sector_eq_halfplanes

end Erdos634.Draft.WedgeWrap
