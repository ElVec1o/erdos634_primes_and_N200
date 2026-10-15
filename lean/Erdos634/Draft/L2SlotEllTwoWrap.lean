import Erdos634.PentagonLemma
import Erdos634.OrderForcing

/-!
# Partner uniqueness and 2b partition: arithmetic kernels

## Partner uniqueness at a slot

`PentagonLemma.partner_unique`: the only non-negative integer solution to
  x·a + y·b + z·c = b   (with a=ef, b=f²−e², c=f², gcd(e,f)=1, e<f)
is (x,y,z) = (0,1,0).  The partner tile presents exactly one b-edge.

## The 2b partition and the east-cover gap

`OrderForcing.partition_2b`: the only non-negative integer solution to
  x·f + y·(f²−1) + z·f² = 2(f²−1)   (f ≥ 3)
is (x,y,z) = (0,2,0).  (Used at the e=1 member a=f, b=f²−1.)

`OrderForcing.east_cover_gap`: no non-negative integer solution to
  x·f + y·(f²−1) + z·f² = f²−1−f   (f ≥ 3)
exists.  (The east-cover gap: the slot-chain advance has no cover.)

The slot chain itself is a placement structure with no definition in this file; only the arithmetic is formalized.

No sorry; standard axioms.
-/

namespace Erdos634.Draft.L2SlotEllTwoWrap

/-- Bundle the arithmetic content of thm:l2slot:
    uniqueness of the b-partner at every slot. -/
theorem l2slot_partner_unique (e f a b c x y z : ℕ)
    (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f)
    (ha : a = e * f) (hb : b + e * e = f * f) (hc : c = f * f)
    (h : x * a + y * b + z * c = b) :
    x = 0 ∧ y = 1 ∧ z = 0 :=
  Erdos634.PentagonLemma.partner_unique hco he hef ha hb hc h

/-- Bundle the arithmetic content of thm:elltwo (partition_2b clause). -/
theorem elltwo_partition_2b (f x y z : ℕ) (hf : 3 ≤ f)
    (h : x * f + y * (f * f - 1) + z * (f * f) = 2 * (f * f) - 2) :
    x = 0 ∧ y = 2 ∧ z = 0 :=
  Erdos634.OrderForcing.partition_2b hf h

/-- Bundle the arithmetic content of thm:elltwo (east_cover_gap clause). -/
theorem elltwo_east_cover_gap (f x y z : ℕ) (hf : 3 ≤ f)
    (h : x * f + y * (f * f - 1) + z * (f * f) = f * f - 1 - f) : False :=
  Erdos634.OrderForcing.east_cover_gap hf h

/-- Non-vacuity for l2slot_partner_unique: (e,f) = (1,2), a=2, b=3, c=4, witness (0,1,0). -/
theorem l2slot_witness : ∃ e f a b c x y z : ℕ,
    Nat.Coprime e f ∧ 1 ≤ e ∧ e < f ∧ a = e * f ∧ b + e * e = f * f ∧ c = f * f ∧
    x * a + y * b + z * c = b ∧ x = 0 ∧ y = 1 ∧ z = 0 :=
  ⟨1, 2, 2, 3, 4, 0, 1, 0,
   by decide, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
   by norm_num, rfl, rfl, rfl⟩

/-- Non-vacuity for elltwo_partition_2b: f = 3, unique solution (0,2,0). -/
theorem elltwo_partition_witness : ∃ f x y z : ℕ,
    3 ≤ f ∧ x * f + y * (f * f - 1) + z * (f * f) = 2 * (f * f) - 2 ∧
    x = 0 ∧ y = 2 ∧ z = 0 :=
  ⟨3, 0, 2, 0, by norm_num, by norm_num, rfl, rfl, rfl⟩

#print axioms l2slot_partner_unique
#print axioms elltwo_partition_2b
#print axioms elltwo_east_cover_gap

end Erdos634.Draft.L2SlotEllTwoWrap
