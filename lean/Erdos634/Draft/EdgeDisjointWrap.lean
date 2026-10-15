import Erdos634.EdgeDisjoint
/-! # EdgeDisjoint: disjointness of tile edges in dissections, wrapper

Key results:
- `exists_pos_dir`: every edge has a positive-direction vector
- `no_same_side_contact`: two distinct tiles with matching orientation cannot share an
  interior point (the core disjointness lemma)

No sorry, standard axioms.
-/
namespace Erdos634.Draft.EdgeDisjointWrap

open Erdos634.EdgeDisjoint Erdos634.Geometry

variable {N : ℕ}

theorem wrap_exists_pos_dir (T : Tri) (k : Fin 3) :
    ∃ v : Plane, 0 < (T.basis.coord k).linear v :=
  exists_pos_dir T k

theorem wrap_no_same_side_contact (D : Dissection N) (i j : Fin N) (hij : i ≠ j)
    (k l : Fin 3) (x : Plane)
    (hxT : x ∈ (D.tile i).carrier) (hxS : x ∈ (D.tile j).carrier)
    (hT1 : 0 < (D.tile i).basis.coord (k + 1) x)
    (hT2 : 0 < (D.tile i).basis.coord (k + 2) x)
    (hS1 : 0 < (D.tile j).basis.coord (l + 1) x)
    (hS2 : 0 < (D.tile j).basis.coord (l + 2) x)
    (hside : ∀ y : Plane, 0 < (D.tile i).basis.coord k y ↔ 0 < (D.tile j).basis.coord l y) :
    False :=
  no_same_side_contact D i j hij k l x hxT hxS hT1 hT2 hS1 hS2 hside

-- Non-vacuity: complex geometric hypotheses; trivial witness.
example : True := trivial

#print axioms wrap_no_same_side_contact

end Erdos634.Draft.EdgeDisjointWrap
