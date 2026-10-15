import Erdos634.Compose

/-!
# Composition of dissections: wrapper

`Compose.compose` builds an `M·N`-piece `Dissection` from an outer `Dissection M`
and inner dissections of each tile.  This is the non-congruent variant of the subdivision
(ladder) construction.

No `sorry`; standard axioms only.
-/

namespace Erdos634.Draft.ComposeWrap

open Erdos634.Compose Erdos634.Geometry

theorem compose_target_eq (M N : ℕ) (D : Dissection M) (inner : Fin M → Dissection N)
    (hin : ∀ i, ((inner i).target).carrier = (D.tile i).carrier) :
    (compose D inner hin).target = D.target :=
  compose_target D inner hin

theorem compose_tile_eq (M N : ℕ) (D : Dissection M) (inner : Fin M → Dissection N)
    (hin : ∀ i, ((inner i).target).carrier = (D.tile i).carrier) (n : Fin (M * N)) :
    (compose D inner hin).tile n
      = (inner (finProdFinEquiv.symm n).1).tile (finProdFinEquiv.symm n).2 :=
  compose_tile D inner hin n

theorem piece_subset_outer (M N : ℕ) (D : Dissection M) (inner : Fin M → Dissection N)
    (hin : ∀ i, ((inner i).target).carrier = (D.tile i).carrier) (i : Fin M) (j : Fin N) :
    ((inner i).tile j).carrier ⊆ (D.tile i).carrier :=
  piece_subset D inner hin i j


#print axioms compose_target_eq
#print axioms compose_tile_eq
#print axioms piece_subset_outer

end Erdos634.Draft.ComposeWrap
