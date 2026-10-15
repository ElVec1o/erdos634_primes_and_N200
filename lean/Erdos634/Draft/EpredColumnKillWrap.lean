import Erdos634.EpredColumnKill

/-!
# EpredColumnKill: e=f−1 column killing, wrapper

Key results:
- `coprime_succ`: e and e+1 are coprime
- `walls_refuted_epred`: walls refuted at e=f−1
- `survivors_23/59/83`: base column equation survivors at N=23,59,83
- `witness_side_23`: non-vacuity witness at (2,3)

No sorry, standard axioms.
-/

namespace Erdos634.Draft.EpredColumnKillWrap

open Erdos634.EpredColumnKill

theorem eck_coprime_succ (e : ℕ) : Nat.Coprime e (e + 1) :=
  coprime_succ e

theorem eck_survivors_23 {x y z : ℤ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 1 ≤ z)
    (hxz : 4 ≤ x + z) (hx2 : 2 ≤ x)
    (h : Erdos634.EpredBaseColumns.BaseEq 3 x y z) : x = 3 ∧ y = 2 ∧ z = 2 :=
  survivors_23 hx hy hz hxz hx2 h

theorem eck_survivors_59 {x y z : ℤ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 1 ≤ z)
    (hxz : 4 ≤ x + z) (hx2 : 2 ≤ x)
    (hwedge : y * (2 * 5 - 1) ^ 2 ≤ 2 * 5 ^ 4 + 2 * 5 ^ 3 - 3 * 5 + 1)
    (h : Erdos634.EpredBaseColumns.BaseEq 5 x y z) :
    (x = 5 ∧ y = 4 ∧ z = 4) ∨ (x = 4 ∧ y = 9 ∧ z = 3) ∨ (x = 3 ∧ y = 14 ∧ z = 2) :=
  survivors_59 hx hy hz hxz hx2 hwedge h

theorem eck_survivors_83 {x y z : ℤ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 1 ≤ z)
    (hxz : 4 ≤ x + z) (hx2 : 2 ≤ x)
    (hwedge : y * (2 * 6 - 1) ^ 2 ≤ 2 * 6 ^ 4 + 2 * 6 ^ 3 - 3 * 6 + 1)
    (h : Erdos634.EpredBaseColumns.BaseEq 6 x y z) :
    (x = 6 ∧ y = 5 ∧ z = 5) ∨ (x = 5 ∧ y = 11 ∧ z = 4) ∨
    (x = 4 ∧ y = 17 ∧ z = 3) ∨ (x = 3 ∧ y = 23 ∧ z = 2) :=
  survivors_83 hx hy hz hxz hx2 hwedge h

theorem eck_witness_side_23 :
    0 * (2 * 3) + 0 * 5 + 3 * (3 * 3) = 3 * 3 * 3 ∧ 2 ≤ 3 :=
  witness_side_23

-- Non-vacuity
example : Nat.Coprime 5 6 := eck_coprime_succ 5

#print axioms eck_survivors_23
#print axioms eck_coprime_succ

end Erdos634.Draft.EpredColumnKillWrap
