import Erdos634.TP_hales

namespace Erdos634.Draft.TP_halesWrap
open Erdos634.TPHales Erdos634.Geometry MeasureTheory
open scoped ENNReal

theorem wrap_restrictOfCount_satisfiable :
    (∀ i ∈ (Finset.univ : Finset (Fin Tiling44.tiles.length)),
        (Tiling44Bridge.dissection.tile i).carrier
          ⊆ Tiling44Bridge.dissection.target.carrier) ∧
      volume Tiling44Bridge.dissection.target.carrier
        = ((Finset.univ : Finset (Fin Tiling44.tiles.length)).card : ℝ≥0∞)
          * volume Tiling44Bridge.dissection.model.carrier :=
  restrictOfCount_satisfiable

example : True := trivial
#check @restrictOfCount_satisfiable

end Erdos634.Draft.TP_halesWrap
