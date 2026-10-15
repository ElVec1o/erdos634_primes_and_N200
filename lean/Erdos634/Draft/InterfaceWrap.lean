import Erdos634.Interface

/-!
# Interface — tile placement interface arithmetic: wrapper

Key results:
- `side_no_b_1_2/3/4`: at small (e,f) members, Q' = 0 (no b on side)
- `no_two_gamma`: at a vertex, at most one γ tile
- `partner_unique_1_2`: at (1,2), the partner tile is unique

No sorry; standard axioms.
-/

namespace Erdos634.Draft.InterfaceWrap

open Erdos634.Interface

theorem iface_side_no_b_1_2 (D : BaseBeta 1 2 1) : D.Q' = 0 :=
  side_no_b_1_2 D

theorem iface_side_no_b_1_3 (D : BaseBeta 1 3 1) : D.Q' = 0 :=
  side_no_b_1_3 D

theorem iface_side_no_b_1_4 (D : BaseBeta 1 4 1) : D.Q' = 0 :=
  side_no_b_1_4 D

theorem iface_no_two_gamma (x y : Nat) : ¬ (x + 2 * 2 = 3 ∧ y + 2 * 2 = 2) :=
  no_two_gamma x y

theorem iface_partner_unique_1_2 (x y z : Nat) (h : x * 2 + y * 3 + z * 4 = 3) :
    x = 0 ∧ y = 1 ∧ z = 0 :=
  partner_unique_1_2 x y z h

#print axioms iface_side_no_b_1_2
#print axioms iface_no_two_gamma
#print axioms iface_partner_unique_1_2

end Erdos634.Draft.InterfaceWrap
