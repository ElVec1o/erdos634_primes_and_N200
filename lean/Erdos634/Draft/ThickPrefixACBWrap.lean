import Erdos634.ThickPrefixACB

namespace Erdos634.Draft.ThickPrefixACBWrap
open Erdos634.ThickPrefixACB
open Erdos634.Geometry Erdos634.CertCoord Erdos634.CertGeom Erdos634.BaseBetaTargetCoord

theorem wrap_blocking_N5 {f : ℝ} (hf : 6 ≤ f) :
    ¬ ((cN5_alpha_bc f hf).carrier ⊆ (tgt f hf).carrier) ∧
    ¬ ((cN5_alpha_cb f hf).carrier ⊆ (tgt f hf).carrier) ∧
    ¬ ((cN5_beta_ac f hf).carrier ⊆ (tgt f hf).carrier) ∧
    ¬ ((cN5_beta_ca f hf).carrier ⊆ (tgt f hf).carrier) ∧
    ¬ ((cN5_gamma_ba f hf).carrier ⊆ (tgt f hf).carrier) :=
  blocking_N5 hf

example : True := trivial
#print axioms wrap_blocking_N5

end Erdos634.Draft.ThickPrefixACBWrap
