import Erdos634.WbtwChain

namespace Erdos634.Draft.WbtwChainWrap
open Erdos634.Geometry Erdos634.ChordTraceReal

-- Wrap at concrete Plane to avoid polymorphic elaboration timeout
theorem wrap_wbtw_chain_bounded {g : ℕ → Plane} (K : ℕ)
    (hchain : ∀ n, n + 2 ≤ K → Wbtw ℝ (g n) (g (n + 1)) (g (n + 2)))
    (hne : ∀ n, n + 1 ≤ K → g n ≠ g (n + 1))
    (hinj : ∀ a b, a ≤ K → b ≤ K → a ≠ b → g a ≠ g b) :
    ∀ i j k, i ≤ j → j ≤ k → k ≤ K → Wbtw ℝ (g i) (g j) (g k) :=
  wbtw_chain_bounded K hchain hne hinj

example : True := trivial
#print axioms wrap_wbtw_chain_bounded

end Erdos634.Draft.WbtwChainWrap
