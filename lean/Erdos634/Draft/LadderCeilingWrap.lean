import Erdos634.LadderCeiling

/-!
# LadderCeiling — L4 gap identity and thick-mixed impossibility: wrapper

Key results:
- `gap_identity`: e·b − L = f²(f−e) algebraic identity
- `gap_lt_eb`: gap is strictly below e·b for 0 < e < f
- `gap_v_ge_e`: b-count of any representation of the gap is ≥ e
- `L4_thick_mixed_impossible`: the mixed A/B corner-cut is impossible in thick regime

No sorry; standard axioms.
-/

namespace Erdos634.Draft.LadderCeilingWrap

open Erdos634.LadderCeiling

theorem lc_gap_identity (e f : ℤ) :
    e * (f ^ 2 - e ^ 2) - (f - e) * (e ^ 2 + e * f - f ^ 2) = f ^ 2 * (f - e) :=
  gap_identity e f

theorem lc_gap_lt_eb {e f : ℤ} (he : 0 < e) (hef : e < f) :
    (f - e) * (e ^ 2 + e * f - f ^ 2) < e * (f ^ 2 - e ^ 2) :=
  gap_lt_eb he hef

theorem lc_gap_v_ge_e {e f v : ℤ} (he : 0 < e) (hef : e < f) (hv : 0 ≤ v)
    (hcong : f ∣ (v - e)) : e ≤ v :=
  gap_v_ge_e he hef hv hcong

theorem lc_L4_thick_mixed_impossible {e f u v w : ℤ} (he : 0 < e) (hef : e < f)
    (hu : 0 ≤ u) (hw : 0 ≤ w) (hv : 0 ≤ v) (hvge : e ≤ v)
    (hrep : (f - e) * (e ^ 2 + e * f - f ^ 2) = u * (e * f) + v * (f ^ 2 - e ^ 2) + w * f ^ 2) :
    False :=
  L4_thick_mixed_impossible he hef hu hw hv hvge hrep

-- Non-vacuity: gap_identity at e=2, f=5
example : (2 : ℤ) * (5 ^ 2 - 2 ^ 2) - (5 - 2) * (2 ^ 2 + 2 * 5 - 5 ^ 2) = 5 ^ 2 * (5 - 2) :=
  lc_gap_identity 2 5

#print axioms lc_gap_lt_eb
#print axioms lc_L4_thick_mixed_impossible

end Erdos634.Draft.LadderCeilingWrap
