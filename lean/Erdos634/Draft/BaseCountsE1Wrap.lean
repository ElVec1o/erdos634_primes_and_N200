import Erdos634.BaseCountsE1

/-!
# e=1 base walk classification: wrapper

`BaseCountsE1.*` provides the e=1 case of the base-walk classification (used in the march).

Key results:
1. **`base_counts`**: the walk na·f+nb·(f²−1)+nc·f²=3f²−1 forces nb=1 with three cases for (na,nc).
2. **`base_counts_corner`**: with nc=2 excluded, only two cases remain.

No `sorry`; standard axioms only.
-/

namespace Erdos634.Draft.BaseCountsE1Wrap

open Erdos634.BaseCountsE1

/-- The e=1 base-walk classification: nb=1 and one of three (na,nc) cases. -/
theorem basecounts_e1 (f na nb nc : ℤ) (hf : 3 ≤ f)
    (hna : 0 ≤ na) (hnb : 0 ≤ nb) (hnc : 0 ≤ nc)
    (heq : na * f + nb * (f ^ 2 - 1) + nc * f ^ 2 = 3 * f ^ 2 - 1) :
    nb = 1 ∧ ((na = 0 ∧ nc = 2) ∨ (na = f ∧ nc = 1) ∨ (na = 2 * f ∧ nc = 0)) :=
  base_counts f na nb nc hf hna hnb hnc heq

/-- With nc=2 excluded, only two cases remain. -/
theorem basecounts_e1_corner (f na nb nc : ℤ) (hf : 3 ≤ f)
    (hna : 0 ≤ na) (hnb : 0 ≤ nb) (hnc : 0 ≤ nc)
    (heq : na * f + nb * (f ^ 2 - 1) + nc * f ^ 2 = 3 * f ^ 2 - 1)
    (hcorner : nc = 2 → False) :
    nb = 1 ∧ ((na = f ∧ nc = 1) ∨ (na = 2 * f ∧ nc = 0)) :=
  base_counts_corner f na nb nc hf hna hnb hnc heq hcorner

/-- Non-vacuity: f=3 satisfies the hypotheses with (na=3, nb=1, nc=1). -/
theorem basecounts_e1_witness : (3:ℤ) * 3 + 1 * (3 ^ 2 - 1) + 1 * 3 ^ 2 = 3 * 3 ^ 2 - 1 := by
  norm_num

#print axioms basecounts_e1
#print axioms basecounts_e1_corner

end Erdos634.Draft.BaseCountsE1Wrap
