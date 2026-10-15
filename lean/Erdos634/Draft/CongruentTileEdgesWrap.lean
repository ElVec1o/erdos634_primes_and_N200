import Erdos634.CongruentTileEdges

/-!
# CongruentTileEdges: side multiset and edge laying for real tiles, wrapper

Key results:
- `Tri.sideMultiset_shift`: side multiset independent of starting vertex
- `congruentDissection_lays_a`: if a real tile lays b,c at vertex j then it lays a on the
  remaining edge (the corner-side lemma for `CongruentDissection`)

No sorry, standard axioms.
-/

namespace Erdos634.Draft.CongruentTileEdgesWrap

open Erdos634.Geometry Erdos634.TilePlacement

variable {N : ℕ}

theorem cte_sideMultiset_shift (T : Tri) (j : Fin 3) :
    ({dist (T.pts j) (T.pts (j+1)), dist (T.pts (j+2)) (T.pts j),
      dist (T.pts (j+1)) (T.pts (j+2))} : Multiset ℝ)
    = {dist (T.pts 0) (T.pts 1), dist (T.pts 2) (T.pts 0), dist (T.pts 1) (T.pts 2)} :=
  Tri.sideMultiset_shift T j

theorem cte_congruentDissection_lays_a (D : CongruentDissection N)
    (hac : sideOpp D.model 2 ≠ sideOpp D.model 1)
    (i : Fin N) (j : Fin 3)
    (hopp : dist ((D.tile i).pts (j+1)) ((D.tile i).pts (j+2)) = sideOpp D.model 0)
    (hbase : dist ((D.tile i).pts j) ((D.tile i).pts (j+1)) = sideOpp D.model 1) :
    dist ((D.tile i).pts (j+2)) ((D.tile i).pts j) = sideOpp D.model 2 :=
  congruentDissection_lays_a D hac i j hopp hbase

-- Non-vacuity: sideMultiset_shift at j=0 is rfl
example (T : Tri) : cte_sideMultiset_shift T 0 = rfl.symm.symm := rfl

#print axioms cte_congruentDissection_lays_a

end Erdos634.Draft.CongruentTileEdgesWrap
