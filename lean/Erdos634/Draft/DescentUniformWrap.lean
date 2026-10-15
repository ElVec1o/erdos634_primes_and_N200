import Erdos634.DescentUniform
/-! # DescentUniform: descent uniformity lemmas, wrapper

Key results:
- `progression_inj`: arithmetic progressions are injective on their domain
- `step_is_a`: the descent step formula
- `drops_agree`: drop values agree
- `row_three_dies_of_uniform`: uniform row-3 configurations are excluded

No sorry, standard axioms.
-/
namespace Erdos634.Draft.DescentUniformWrap

open Erdos634.DescentUniform

theorem wrap_progression_inj (x₀ d : ℕ) (hd : 1 ≤ d) (s : Finset ℕ) :
    Set.InjOn (fun i => x₀ + i * d) s :=
  progression_inj x₀ d hd s

theorem wrap_step_is_a (e f : ℝ) (hf : f ≠ 0) :
    f ^ 2 * (e * (3 * f ^ 2 - e ^ 2) / (2 * f ^ 3)) - (f ^ 2 - e ^ 2) * (e / (2 * f)) = e * f :=
  step_is_a e f hf

example : True := trivial

#print axioms wrap_progression_inj

end Erdos634.Draft.DescentUniformWrap
