import Erdos634.TangentCone

namespace Erdos634.Draft.TangentConeWrap
open Erdos634.TangentCone

theorem wrap_slack_ratio {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} (f : Fin n → E →L[ℝ] ℝ) (c : Fin n → ℝ) (p : E) (i : Fin n)
    (hi : f i p < c i) (hf : 0 < ‖f i‖) {ρ : ℝ} (hρ : ρ ≤ (c i - f i p) / ‖f i‖) :
    ‖f i‖ * ρ ≤ c i - f i p :=
  slack_ratio f c p i hi hf hρ

example : True := trivial
#check @wrap_slack_ratio

end Erdos634.Draft.TangentConeWrap
