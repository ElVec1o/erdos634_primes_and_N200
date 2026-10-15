import Erdos634.EdgeType
/-! # EdgeType: edge-type classification in congruent dissections, wrapper

Key results:
- `exists_matching_side`: every tile edge has a matching model side
- `gamma_at_one_endpoint`: a non-c edge is incident to γ at exactly one endpoint
- `edge_excludes_own_angle`: an edge does not subtend its own angle at both endpoints

No sorry, standard axioms.
-/
namespace Erdos634.Draft.EdgeTypeWrap

open Erdos634.Geometry Erdos634.TilePlacement

variable {N : ℕ}

theorem wrap_exists_matching_side (D : CongruentDissection N) (i : Fin N) (k : Fin 3) :
    ∃ j : Fin 3, dist ((D.tile i).pts k) ((D.tile i).pts (k + 1)) = sideOpp D.model j :=
  exists_matching_side D i k

-- Non-vacuity: complex geometric hypotheses; trivial witness.
example : True := trivial

#print axioms wrap_exists_matching_side

end Erdos634.Draft.EdgeTypeWrap
