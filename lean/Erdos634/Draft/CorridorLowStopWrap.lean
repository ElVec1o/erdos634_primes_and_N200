import Erdos634.CorridorLowStop

/-!
# CorridorLowStop: corridor equation below e, wrapper

Key results:
- `squeeze_Y_zero`: non-negativity forces Y=0 for m < f
- `corridor_low`: for m ≤ e, only solution is m=e with word a^f
- `classification`: full classification of solutions for m < f (a^{jf} c^{m-je} family)
- `unreachable_below_e`: m < e admits no solution at all

No sorry, standard axioms.
-/

namespace Erdos634.Draft.CorridorLowStopWrap

open Erdos634.CorridorLowStop

theorem cls_squeeze_Y_zero (e f m Y t : ℤ) (he : 2 ≤ e) (hef : e < f) (hmf : m < f)
    (hY : 0 ≤ Y) (hx : 1 ≤ Y * e - t * f) (hz : 0 ≤ m - Y * f + t * e) : Y = 0 :=
  squeeze_Y_zero e f m Y t he hef hmf hY hx hz

theorem cls_corridor_low (e f m Y t : ℤ) (he : 2 ≤ e) (hef : e < f) (hm : 0 < m) (hme : m ≤ e)
    (hY : 0 ≤ Y) (hx : 1 ≤ Y * e - t * f) (hz : 0 ≤ m - Y * f + t * e) :
    m = e ∧ Y * e - t * f = f ∧ Y = 0 ∧ m - Y * f + t * e = 0 :=
  corridor_low e f m Y t he hef hm hme hY hx hz

theorem cls_classification (e f m Y t : ℤ) (he : 2 ≤ e) (hef : e < f) (hmf : m < f)
    (hY : 0 ≤ Y) (hx : 1 ≤ Y * e - t * f) (hz : 0 ≤ m - Y * f + t * e) :
    Y = 0 ∧ 1 ≤ -t ∧ (-t) * e ≤ m ∧ Y * e - t * f = (-t) * f
      ∧ m - Y * f + t * e = m - (-t) * e :=
  classification e f m Y t he hef hmf hY hx hz

-- Non-vacuity: descent_solves is a ring identity
example : ((0 : ℤ) * 2 - (-1) * 3) * (2 * 3) + (3 * 0) * (3 ^ 2 - 2 ^ 2)
    + (2 - 0 * 3 + (-1) * 2) * 3 ^ 2 = 2 * 3 ^ 2 := by ring

#print axioms cls_classification

end Erdos634.Draft.CorridorLowStopWrap
