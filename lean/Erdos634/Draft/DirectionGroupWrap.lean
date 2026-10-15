import Erdos634.DirectionGroup
/-! # DirectionGroup: lattice of direction vectors, wrapper

Key results:
- `L_relation`: the bilinear form vanishes on the diagonal
- `L_surjective`: surjectivity of the direction functional
- `L_ker`: kernel characterisation
- `L_basebeta`: base-β specialisation
- `basebeta_coprime`: (3, 2) are coprime as integers
- `torsion_iff`: torsion characterisation in terms of L

No sorry, standard axioms.
-/
namespace Erdos634.Draft.DirectionGroupWrap

open Erdos634.DirectionGroup

theorem wrap_L_relation (p q : ℤ) : L p q p q = 0 :=
  L_relation p q

theorem wrap_L_basebeta (x y : ℤ) : L 3 2 x y = 2 * x - 3 * y :=
  L_basebeta x y

theorem wrap_basebeta_coprime : IsCoprime (3 : ℤ) 2 :=
  basebeta_coprime

-- Non-vacuity: the relation holds on a concrete pair.
example : L 3 2 3 2 = 0 := L_relation 3 2

#print axioms wrap_L_relation

end Erdos634.Draft.DirectionGroupWrap
