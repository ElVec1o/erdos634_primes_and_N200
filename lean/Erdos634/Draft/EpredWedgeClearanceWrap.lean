import Erdos634.EpredWedgeClearance

namespace Erdos634.Draft.EpredWedgeClearanceWrap

open Erdos634.EpredWedgeClearance

theorem ewc_clearNum_b (e f : ℤ) :
    clearNum e f (sb e f) (sc e f) (sa e f) = 2 * (sa e f ^ 2 - sb e f ^ 2) :=
  clearNum_b e f

theorem ewc_clearNum_a (e f : ℤ) : clearNum e f (sa e f) (sc e f) (sb e f) = 0 :=
  clearNum_a e f

theorem ewc_clearance_pos_iff_subGolden {e f : ℤ} (ha : 0 < sa e f) (hb : 0 < sb e f) :
    0 < sa e f ^ 2 - sb e f ^ 2 ↔ sb e f < sa e f :=
  clearance_pos_iff_subGolden ha hb

theorem ewc_a_lt_c {e f : ℤ} (he : 0 < e) (hef : e < f) : sa e f < sc e f :=
  a_lt_c he hef

example : True := trivial

#print axioms ewc_a_lt_c
#print axioms ewc_clearance_pos_iff_subGolden

end Erdos634.Draft.EpredWedgeClearanceWrap
