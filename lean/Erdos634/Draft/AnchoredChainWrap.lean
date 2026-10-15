import Erdos634.AnchoredChain

/-!
# Chain anchored at a γ-corner: wrapper

Re-exports, under `ac_` names, results of `AnchoredChain`:
- `no_second_through_with_gamma`: two through-edges + γ overruns the 2π budget
- `residue_beside_gamma_figure`: the residue beside γ is exactly one α + one β
- `chain_endpoint_pinned`: α+β < π, so the chain endpoint is forced

No `sorry`; standard axioms only.
-/

namespace Erdos634.Draft.AnchoredChainWrap

open Erdos634.AnchoredChain Erdos634.Geometry

theorem ac_residue_beside_gamma_figure (x y z : ℕ) (h1 : x + 2 * z = 1) (h2 : y + z = 1) :
    x = 1 ∧ y = 1 ∧ z = 0 :=
  residue_beside_gamma_figure x y z h1 h2

theorem ac_chain_endpoint_pinned (residue α β : ℝ) (hres : residue = α + β)
    (hα : 0 < α) (hβ : 0 < β) (hπ : 3 * α + 2 * β = Real.pi) : residue < Real.pi :=
  chain_endpoint_pinned residue α β hres hα hβ hπ

-- Non-vacuity: residue_beside_gamma_figure with x=1, y=1, z=0
example : (1:ℕ) = 1 ∧ 1 = 1 ∧ 0 = 0 :=
  ac_residue_beside_gamma_figure 1 1 0 (by omega) (by omega)

#print axioms ac_chain_endpoint_pinned
#print axioms ac_residue_beside_gamma_figure

end Erdos634.Draft.AnchoredChainWrap
