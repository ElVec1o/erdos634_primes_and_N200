import Erdos634.OrderForcing

/-!
# The shadow at a c-corner: wrapper

If a base corner tile lays c on the base and the first
side run has length ≥ 2, every base edge in the shadow is a c-edge. At e=1 the two-sided shadow
window is always smaller than the b-edge (3f²>1), an independent exclusion of c-corners; at e≥2
the comparison reverses.

The arithmetic kernel:
1. `shadow_footage_e1` (OrderForcing): at e=1, (3f²-1)(f²-1) - 2f⁴ < (f²-1)f², i.e. the
   shadow window is too small for the b-edge, for all f≥2.

This module contains the arithmetic kernel only.  The strip geometry (strip tiles span the strip, c on floor or
ceiling, parallel sides argument) and the identification of the base edges meeting the shadow as c-edges are
placement statements and are not part of it.

0 sorry, standard axioms.
-/

namespace Erdos634.Draft.ShadowWrap

open Erdos634.OrderForcing

/-- lem:shadow (e=1 arithmetic): the shadow window at e=1 is always smaller than b (shadow_footage_e1). -/
theorem shadow_footage_e1_wrap (f : ℤ) (hf : 2 ≤ f) :
    (3 * f ^ 2 - 1) * (f ^ 2 - 1) - 2 * f ^ 4 < (f ^ 2 - 1) * f ^ 2 :=
  shadow_footage_e1 f hf

/-- lem:shadow (3f²>1): the comparison that kills c-corners at e=1 simplifies to 3f²>1. -/
theorem shadow_3f2_gt_one (f : ℤ) (hf : 2 ≤ f) : 1 < 3 * f ^ 2 := by nlinarith

#print axioms shadow_footage_e1_wrap
#print axioms shadow_3f2_gt_one

end Erdos634.Draft.ShadowWrap
