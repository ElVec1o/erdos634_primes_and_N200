/-
Draft/CensusScope.lean -- the census identity on a real tiling.

`LemCensusFormal.lem_census_exact` gives the identity `v₁ = 1 + n₂ + v₃ + 2 v₄` for every congruent dissection of a
target with two corners `β` (every scale).  Here it is instantiated on the kernel-checked 44-tiling
(`ApexWitness44.D44`: 44 copies of `(2,3,4)` in `(16,16,22)`, member `(1,2)`, scale 2), every hypothesis discharged:

    theorem census_on_44 : v₁ = 1 + n₂ + v₃ + 2 v₄  ∧  1 ≤ v₁      (counts of `D44`)

and the fills of the three target corners (`corners_on_44`).
`LemCensusFormal.census_equations_equiv` states that, given the α-balance, the β- and γ-balance equations together
are equivalent to the identity.  No sorry, no native_decide.
-/
import Erdos634.Draft.LemCensusFormal
import Erdos634.Draft.GammaTrapWitness44

namespace Erdos634.Draft.CensusScope

open Erdos634.Geometry Erdos634.Z15Real Erdos634.Tiling44Bridge Erdos634.BaseBetaTargetCoord
open Erdos634.Draft.ApexWitness44 Erdos634.Draft.GammaTrapWitness44 Erdos634.Draft.LemCensusFormal

/-- **The census identity on the real 44-tiling**: `v₁ = 1 + n₂ + v₃ + 2 v₄`, and `v₁ ≥ 1`. -/
theorem census_on_44 :
    cnt D44 (modelAlpha 1 ((2 : ℕ) : ℝ)) (modelBeta 1 ((2 : ℕ) : ℝ))
        (2 * modelAlpha 1 ((2 : ℕ) : ℝ) + modelBeta 1 ((2 : ℕ) : ℝ)) (0, 1, 3)
      = 1 + cnt D44 (modelAlpha 1 ((2 : ℕ) : ℝ)) (modelBeta 1 ((2 : ℕ) : ℝ))
            (2 * modelAlpha 1 ((2 : ℕ) : ℝ) + modelBeta 1 ((2 : ℕ) : ℝ)) (3, 2, 0)
        + cnt D44 (modelAlpha 1 ((2 : ℕ) : ℝ)) (modelBeta 1 ((2 : ℕ) : ℝ))
            (2 * modelAlpha 1 ((2 : ℕ) : ℝ) + modelBeta 1 ((2 : ℕ) : ℝ)) (4, 3, 1)
        + 2 * cnt D44 (modelAlpha 1 ((2 : ℕ) : ℝ)) (modelBeta 1 ((2 : ℕ) : ℝ))
            (2 * modelAlpha 1 ((2 : ℕ) : ℝ) + modelBeta 1 ((2 : ℕ) : ℝ)) (6, 4, 0) ∧
    1 ≤ cnt D44 (modelAlpha 1 ((2 : ℕ) : ℝ)) (modelBeta 1 ((2 : ℕ) : ℝ))
        (2 * modelAlpha 1 ((2 : ℕ) : ℝ) + modelBeta 1 ((2 : ℕ) : ℝ)) (0, 1, 3) := by
  have h := lem_census_exact D44 D44_angleData D44_hα D44_hβ D44_hγ 2 tgt_hb0 tgt_hb1
  exact ⟨h.2.2.2.2.1, h.2.2.2.2.2⟩

/-- the three corners of the 44-target are filled as the lemma says: three `α` at the apex, one `β` at each base
corner -/
theorem corners_on_44 :
    fig D44 (modelAlpha 1 ((2 : ℕ) : ℝ)) (modelBeta 1 ((2 : ℕ) : ℝ))
        (2 * modelAlpha 1 ((2 : ℕ) : ℝ) + modelBeta 1 ((2 : ℕ) : ℝ)) (D44.target.pts 2) = (3, 0, 0) ∧
    fig D44 (modelAlpha 1 ((2 : ℕ) : ℝ)) (modelBeta 1 ((2 : ℕ) : ℝ))
        (2 * modelAlpha 1 ((2 : ℕ) : ℝ) + modelBeta 1 ((2 : ℕ) : ℝ)) (D44.target.pts (2 + 1)) = (0, 1, 0) ∧
    fig D44 (modelAlpha 1 ((2 : ℕ) : ℝ)) (modelBeta 1 ((2 : ℕ) : ℝ))
        (2 * modelAlpha 1 ((2 : ℕ) : ℝ) + modelBeta 1 ((2 : ℕ) : ℝ)) (D44.target.pts (2 + 2)) = (0, 1, 0) := by
  have h := lem_census_exact D44 D44_angleData D44_hα D44_hβ D44_hγ 2 tgt_hb0 tgt_hb1
  exact ⟨h.2.1, h.2.2.1, h.2.2.2.1⟩

end Erdos634.Draft.CensusScope

#print axioms Erdos634.Draft.CensusScope.census_on_44
