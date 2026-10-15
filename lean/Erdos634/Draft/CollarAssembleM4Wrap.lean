import Erdos634.CollarAssembleM4

/-!
# Assembly of the M=4 collar dissection

Re-exports results of `CollarAssembleM4`: `delta4Dissection`, a valid `Dissection 176` built from the
176 collar pieces.  Supporting: `delta4Pieces_pairwise` (pairwise disjoint interiors) and
`delta4Pieces_subset_delta4` (all pieces contained in `delta4`).

No `sorry`.
-/

namespace Erdos634.Draft.CollarAssembleM4Wrap

open Erdos634.Geometry Erdos634.CertCoord Erdos634.DissectionMap Erdos634.CertGeom
open Erdos634.Realizable Erdos634.TranslateDissection Erdos634.AreaDet

/-- Wrap: all 176 pieces lie inside `delta4`. -/
theorem delta4Pieces_subset_delta4_wrap :
    ∀ i : Fin 176, (delta4Pieces i).carrier ⊆ delta4.carrier :=
  delta4Pieces_subset_delta4

/-- Wrap: the 176 pieces have pairwise disjoint interiors. -/
theorem delta4Pieces_pairwise_wrap :
    Pairwise (fun i j : Fin 176 => Disjoint (interior (delta4Pieces i).carrier)
      (interior (delta4Pieces j).carrier)) :=
  delta4Pieces_pairwise

/-- Wrap: `delta4Dissection` is a valid `Dissection 176`. -/
noncomputable def delta4Dissection_wrap : Dissection 176 := delta4Dissection

example : True := trivial

#print axioms delta4Pieces_pairwise_wrap
#print axioms delta4Pieces_subset_delta4_wrap

end Erdos634.Draft.CollarAssembleM4Wrap
