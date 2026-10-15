import Erdos634.DualGraph44

/-!
# Numeric invariants of the N=44 dual graph

Three numeric facts about the dual graph of the 44-tile tiling, checked by the kernel against the coordinates in `Tiling44.tiles`:

1. 45 shared edges: `spectral_edge_count` (`totalSharedEdges_eq_45`, by `decide`).
2. Degree distribution {1:12, 2:18, 3:14}: `spectral_degree_distribution`; the distribution {1:11, 2:20, 3:13} is excluded by `spectral_paper_distribution_wrong`.
3. Component sizes [2,4,8,14,16]: `spectral_component_sizes`; the sizes [4,8,16,16] are excluded by `spectral_paper_component_sizes_wrong`.

The statement that spectral invariants of the dual graph cannot answer the crossing question is a meta-argument and is not formalized.

Axioms: [propext], 0 sorry.
-/

namespace Erdos634.Draft.SpectralWrap

open Erdos634.DualGraph44

/-- The N=44 dual graph has exactly 45 shared full edges. -/
theorem spectral_edge_count : totalSharedEdges = 45 :=
  totalSharedEdges_eq_45

/-- Degree distribution: {1:12, 2:18, 3:14} — corrects the paper's {1:11, 2:20, 3:13}. -/
theorem spectral_degree_distribution :
    ((List.finRange 44).filter fun i => degree i == 1).length = 12 ∧
    ((List.finRange 44).filter fun i => degree i == 2).length = 18 ∧
    ((List.finRange 44).filter fun i => degree i == 3).length = 14 ∧
    (List.finRange 44).all (fun i => degree i == 1 || degree i == 2 || degree i == 3) :=
  degree_distribution

/-- The paper's claimed distribution {1:11,2:20,3:13} is FALSE. -/
theorem spectral_paper_distribution_wrong :
    ¬ (((List.finRange 44).filter fun i => degree i == 1).length = 11 ∧
       ((List.finRange 44).filter fun i => degree i == 2).length = 20 ∧
       ((List.finRange 44).filter fun i => degree i == 3).length = 13) :=
  paper_distribution_wrong

/-- Component sizes [2,4,8,14,16] — corrects the paper's [4,8,16,16]. -/
theorem spectral_component_sizes :
    isortNat ((List.finRange 44).map componentOf |>.dedup |>.map (fun l => l.length))
      = [2, 4, 8, 14, 16] :=
  component_sizes

/-- The paper's claimed component sizes [4,8,16,16] are FALSE. -/
theorem spectral_paper_component_sizes_wrong :
    isortNat ((List.finRange 44).map componentOf |>.dedup |>.map (fun l => l.length))
      ≠ [4, 8, 16, 16] :=
  paper_component_sizes_wrong

#print axioms spectral_edge_count
#print axioms spectral_degree_distribution
#print axioms spectral_component_sizes

end Erdos634.Draft.SpectralWrap
