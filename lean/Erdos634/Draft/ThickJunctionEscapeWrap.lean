import Erdos634.ThickJunctionEscape

namespace Erdos634.Draft.ThickJunctionEscapeWrap
open Erdos634.ThickJunctionEscape
open Erdos634.Geometry Erdos634.CertCoord Erdos634.CertGeom Erdos634.ThickPrefixACB

theorem wrap_witness_83 :
    (66 : ℝ) < D0a 6 ∧ (66 : ℝ) < D0ab 6 ∧
    mkPt (Lq 6 - 66) 0 ∈ (tgt 6 (le_refl 6)).carrier ∧
    ¬ ((cJ_alpha_cb 6 (le_refl 6) 66).carrier ⊆ (tgt 6 (le_refl 6)).carrier) ∧
    ¬ ((cJ_alpha_bc 6 (le_refl 6) 66).carrier ⊆ (tgt 6 (le_refl 6)).carrier) ∧
    ¬ ((cJ_beta_ca 6 (le_refl 6) 66).carrier ⊆ (tgt 6 (le_refl 6)).carrier) ∧
    ¬ ((cJ_beta_ac 6 (le_refl 6) 66).carrier ⊆ (tgt 6 (le_refl 6)).carrier) :=
  witness_83

example : True := trivial
#print axioms wrap_witness_83

end Erdos634.Draft.ThickJunctionEscapeWrap
