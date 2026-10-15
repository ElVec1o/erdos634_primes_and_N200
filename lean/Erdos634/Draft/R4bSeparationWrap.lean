import Erdos634.R4bSeparation

namespace Erdos634.Draft.R4bSeparationWrap
open Erdos634.R4bSeparation

theorem wrap_crossing_budget
    {a b c lenS X Kb M : ℝ} {na nb nc f j : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hlen : lenS = na * a + nb * b + nc * c + X)
    (hnbj : (j : ℝ) ≤ nb) (hjf : (f : ℝ) ≤ j) (hKb : Kb = f * b)
    (hmax : lenS ≤ M) :
    X ≤ M - Kb :=
  crossing_budget ha hb hc hlen hnbj hjf hKb hmax

example : True := trivial
#print axioms wrap_crossing_budget

end Erdos634.Draft.R4bSeparationWrap
