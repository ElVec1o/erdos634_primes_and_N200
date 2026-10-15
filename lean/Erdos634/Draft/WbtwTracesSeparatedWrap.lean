import Erdos634.WbtwTracesSeparated

namespace Erdos634.Draft.WbtwTracesSeparatedWrap
open Erdos634.ChordTraceReal Erdos634.Geometry

theorem wrap_traces_separated_of_disjoint {p q r₁ s₁ r₂ s₂ : Plane}
    (hr1 : Wbtw ℝ p r₁ q) (hs1 : Wbtw ℝ p s₁ q) (hr2 : Wbtw ℝ p r₂ q) (hs2 : Wbtw ℝ p s₂ q)
    (hr1s1 : r₁ ≠ s₁) (hr2s2 : r₂ ≠ s₂)
    (ho1 : Wbtw ℝ p r₁ s₁) (ho2 : Wbtw ℝ p r₂ s₂)
    (hdisj : (segment ℝ r₁ s₁ ∩ segment ℝ r₂ s₂).Subsingleton) :
    Wbtw ℝ p s₁ r₂ ∨ Wbtw ℝ p s₂ r₁ :=
  traces_separated_of_disjoint hr1 hs1 hr2 hs2 hr1s1 hr2s2 ho1 ho2 hdisj

example : True := trivial
#check @wrap_traces_separated_of_disjoint

end Erdos634.Draft.WbtwTracesSeparatedWrap
