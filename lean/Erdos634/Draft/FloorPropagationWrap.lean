import Erdos634.FloorPropagation

namespace Erdos634.Draft.FloorPropagationWrap
open Erdos634.FloorPropagation
open Finset

theorem wrap_reaches_base_of_uniform_below (f : ℕ) (hf : 3 ≤ f) (isA : ℕ → Prop)
    [DecidablePred isA]
    (base_count : ((range (f + 2)).filter isA).card = f)
    (x₀ : ℕ)
    (uniform_below : ∀ i ∈ range (f + 1), x₀ + i * f < f + 2 ∧ isA (x₀ + i * f)) :
    False :=
  reaches_base_of_uniform_below f hf isA base_count x₀ uniform_below

example : True := trivial
#check @wrap_reaches_base_of_uniform_below

end Erdos634.Draft.FloorPropagationWrap
