import Erdos634.ThinCaseAnalysis

namespace Erdos634.Draft.ThinCaseAnalysisWrap
open Erdos634.ThinCaseAnalysis

theorem wrap_no_configuration_survives
    (f : ℕ) (L R : Side) (hL : 1 ≤ L.l) (hR : 1 ≤ R.l)
    (Z : L.p = 0 → R.p = 0 → False)
    (D : ∀ s : Side, 1 ≤ s.p → 2 ≤ s.l → False)
    (C : ∀ s t : Side, 1 ≤ s.p → s.l = 1 → (t.p = 0 ∨ t.l = 1) → False) :
    False :=
  no_configuration_survives f L R hL hR Z D C

example : True := trivial
#print axioms wrap_no_configuration_survives

end Erdos634.Draft.ThinCaseAnalysisWrap
