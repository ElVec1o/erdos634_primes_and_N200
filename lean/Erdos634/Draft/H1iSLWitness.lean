/-
Satisfiability check for `H1iSLMain`.
On the real `CongruentDissection 2` `dissection'` (used by `H1Witnesses`), with `K = ⊤` and `ψ = id`, every hypothesis of
`side_sign_lemma` holds (so SL is not vacuous) and its conclusion is instantiated.  This does NOT exhibit a nontrivial
conjugation (`ψ ≠ id`); a witness with `K = ℚ(√M)`, `ψ = σ` needs a dissection with corners in a quadratic field
(for instance a tiling for N = 10) and is not built here.
 No sorry.
-/
import Erdos634.Draft.H1iSLMain
import Erdos634.Draft.FluxGRow3RPAnyLabelWitness

namespace Erdos634.H1iSL.Witness

open Erdos634.Geometry Erdos634.Draft.FluxGRow3WitnessBridge

theorem sl_witness (s : Fin 3) :
    ∃ (part : Finset (Fin 2 × Fin 3)) (hL : dist (dissection'.target.pts s) (dissection'.target.pts (s + 1)) ∈
        (⊤ : Subfield ℝ)),
      ∀ e ∈ part, 0 < (Subfield.topEquiv.toRingHom : (⊤ : Subfield ℝ) →+* ℝ)
          ⟨dist ((dissection'.tile e.1).pts e.2) ((dissection'.tile e.1).pts (e.2 + 1)), trivial⟩ *
        (Subfield.topEquiv.toRingHom : (⊤ : Subfield ℝ) →+* ℝ)
          ⟨dist (dissection'.target.pts s) (dissection'.target.pts (s + 1)), hL⟩ := by
  obtain ⟨part, hL, -, -, -, -, hpos, -⟩ := side_sign_lemma dissection' (⊤ : Subfield ℝ)
    Subfield.topEquiv.toRingHom (fun _ _ _ => trivial) (fun _ _ => trivial) (fun _ _ => trivial) s
  exact ⟨part, hL, hpos⟩

end Erdos634.H1iSL.Witness

#print axioms Erdos634.H1iSL.Witness.sl_witness
