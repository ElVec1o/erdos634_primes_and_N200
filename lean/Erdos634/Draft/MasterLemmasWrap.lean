import Erdos634.MasterLemmas

/-!
# MasterLemmas — inter-apex uniqueness and equal footprints: wrapper

Key results:
- `interapex_e*f*`: inter-apex uniqueness for specific (e,f) frontier members
- `feet_e*f*`: equal footprints and T_mid for specific (e,f) members

No sorry; standard axioms.
-/

namespace Erdos634.Draft.MasterLemmasWrap

open Erdos634.MasterLemmas

theorem ml_interapex_e2f3 : ∀ x y z : Nat, x*6 + y*5 + z*9 = 6 → x = 1 ∧ y = 0 ∧ z = 0 :=
  interapex_e2f3

theorem ml_interapex_e4f5 : ∀ x y z : Nat, x*20 + y*9 + z*25 = 20 → x = 1 ∧ y = 0 ∧ z = 0 :=
  interapex_e4f5

theorem ml_interapex_e5f6 : ∀ x y z : Nat, x*30 + y*11 + z*36 = 30 → x = 1 ∧ y = 0 ∧ z = 0 :=
  interapex_e5f6

theorem ml_interapex_e4f7 : ∀ x y z : Nat, x*28 + y*33 + z*49 = 28 → x = 1 ∧ y = 0 ∧ z = 0 :=
  interapex_e4f7

theorem ml_interapex_e2f9 : ∀ x y z : Nat, x*18 + y*77 + z*81 = 18 → x = 1 ∧ y = 0 ∧ z = 0 :=
  interapex_e2f9

theorem ml_interapex_e4f9 : ∀ x y z : Nat, x*36 + y*65 + z*81 = 36 → x = 1 ∧ y = 0 ∧ z = 0 :=
  interapex_e4f9

theorem ml_interapex_e7f10 : ∀ x y z : Nat, x*70 + y*51 + z*100 = 70 → x = 1 ∧ y = 0 ∧ z = 0 :=
  interapex_e7f10

theorem ml_feet_e2f3 : 2*9 = 3*6 ∧ 2*(3*9-4) - 2*(2*9) = 2*5 := feet_e2f3
theorem ml_feet_e4f5 : 4*25 = 5*20 ∧ 4*(3*25-16) - 2*(4*25) = 4*9 := feet_e4f5
theorem ml_feet_e5f6 : 5*36 = 6*30 ∧ 5*(3*36-25) - 2*(5*36) = 5*11 := feet_e5f6
theorem ml_feet_e4f7 : 4*49 = 7*28 ∧ 4*(3*49-16) - 2*(4*49) = 4*33 := feet_e4f7
theorem ml_feet_e2f9 : 2*81 = 9*18 ∧ 2*(3*81-4) - 2*(2*81) = 2*77 := feet_e2f9
theorem ml_feet_e4f9 : 4*81 = 9*36 ∧ 4*(3*81-16) - 2*(4*81) = 4*65 := feet_e4f9

-- Non-vacuity: feet_e2f3 is a closed ground proposition
example : 2*9 = 3*6 ∧ 2*(3*9-4) - 2*(2*9) = 2*5 := ml_feet_e2f3

#print axioms ml_interapex_e2f3
#print axioms ml_feet_e4f9

end Erdos634.Draft.MasterLemmasWrap
