import Erdos634.CollarCongruentM4

/-!
# Congruent dissection for the M=4 collar

Re-exports results of `CollarCongruentM4`: `delta4CongruentDissection`, a valid `CongruentDissection 176`
for the delta-4 collar, with all 176 pieces congruent to the Tiling44 model piece.

No `sorry`.
-/

namespace Erdos634.Draft.CollarCongruentM4Wrap

open Erdos634.Geometry Erdos634.CertCoord Erdos634.DissectionMap Erdos634.AreaDet
open Erdos634.Realizable Erdos634.TranslateDissection

/-- Wrap: all 176 collar pieces are congruent to the Tiling44 model piece. -/
theorem delta4Pieces_congruent_wrap :
    ∀ i : Fin 176, (delta4Pieces i).Congruent
      (Erdos634.Tiling44Bridge.pieceTri Erdos634.Tiling44Bridge.headI_mem_tiles) :=
  delta4Pieces_congruent

/-- Wrap: `delta4CongruentDissection` is a valid `CongruentDissection 176`. -/
noncomputable def delta4CongruentDissection_wrap : CongruentDissection 176 :=
  delta4CongruentDissection

example : True := trivial

#print axioms delta4Pieces_congruent_wrap

end Erdos634.Draft.CollarCongruentM4Wrap
