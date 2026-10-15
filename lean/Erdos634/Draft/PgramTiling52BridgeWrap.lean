import Erdos634.PgramTiling52Bridge

namespace Erdos634.Draft.PgramTiling52BridgeWrap
open Erdos634.Geometry
open Erdos634.PgramTiling52Bridge

theorem wrap_covers_of_volume {N : ℕ} (tile : Fin N → Tri)
    (hsub : ∀ i, (tile i).carrier ⊆ carrier)
    (hdisj : Pairwise fun i j => Disjoint (interior (tile i).carrier) (interior (tile j).carrier))
    (hvol : ∑ i, MeasureTheory.volume (tile i).carrier = MeasureTheory.volume carrier) :
    (⋃ i, (tile i).carrier) = carrier :=
  covers_of_volume tile hsub hdisj hvol

example : True := trivial
#print axioms wrap_covers_of_volume

end Erdos634.Draft.PgramTiling52BridgeWrap
