import Erdos634.RegionWitness

namespace Erdos634.Draft.RegionWitnessWrap
open Erdos634.RegionWitness

theorem wrap_witness_pieces_nonempty :
    (interior (singleTile (Erdos634.Tiling44Bridge.dissection.toDissection.tile
      ⟨0, Nat.zero_lt_of_lt fortyfour_two_tiles⟩)).region).Nonempty
    ∧ (interior (singleTile (Erdos634.Tiling44Bridge.dissection.toDissection.tile
        ⟨1, fortyfour_two_tiles⟩)).region).Nonempty :=
  witness_pieces_nonempty

example : True := trivial
#print axioms wrap_witness_pieces_nonempty

end Erdos634.Draft.RegionWitnessWrap
