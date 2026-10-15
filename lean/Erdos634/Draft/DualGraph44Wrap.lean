import Erdos634.DualGraph44

/-!
# DualGraph44: dual graph of the N=44 tiling, wrapper

Key results:
- `totalSharedEdges_eq_45`: the 44-tiling has exactly 45 shared edges
- `degree_distribution`: {1:12, 2:18, 3:14}
- `paper_distribution_wrong`: the distribution {1:11, 2:20, 3:13} does not match the certified coordinates

No sorry, standard axioms.
-/

namespace Erdos634.Draft.DualGraph44Wrap

open Erdos634.DualGraph44

theorem dg44_tiles_length : Tiling44.tiles.length = 44 := tiles_length

theorem dg44_totalSharedEdges_eq_45 : totalSharedEdges = 45 := totalSharedEdges_eq_45

theorem dg44_degree_distribution :
    ((List.finRange 44).filter fun i => degree i == 1).length = 12 ∧
    ((List.finRange 44).filter fun i => degree i == 2).length = 18 ∧
    ((List.finRange 44).filter fun i => degree i == 3).length = 14 ∧
    (List.finRange 44).all (fun i => degree i == 1 || degree i == 2 || degree i == 3) :=
  degree_distribution

theorem dg44_paper_distribution_wrong :
    ¬ (((List.finRange 44).filter fun i => degree i == 1).length = 11 ∧
       ((List.finRange 44).filter fun i => degree i == 2).length = 20 ∧
       ((List.finRange 44).filter fun i => degree i == 3).length = 13) :=
  paper_distribution_wrong

-- Non-vacuity: totalSharedEdges is a ground decide fact
example : totalSharedEdges = 45 := dg44_totalSharedEdges_eq_45

#print axioms dg44_degree_distribution
#print axioms dg44_paper_distribution_wrong

end Erdos634.Draft.DualGraph44Wrap
