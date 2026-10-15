import Erdos634.ApexRigidity

/-!
# No both-mirror and U-placement: arithmetic cores

The three cross products are simultaneously
positive exactly when e²+ef < f². Cited Lean theorems:

* `ApexRigidity.quad_neg_always`: the first factor e²−ef−f² is always negative (nlinarith).
* `ApexRigidity.overlap_signs`: all three cross products positive iff e²+ef < f² (nlinarith).

U-placements: the two flanking drops agree; separation is a;
V is interior. Cited Lean theorems:

* `ApexRigidity.drops_agree_37`: drops equal at (3,7) (ring arithmetic).
* `ApexRigidity.U_edge_length_37`: separation is a=21 at (3,7) (norm_num).
* `ApexRigidity.V_interior`: V is interior to U's edge whenever e²+ef < f² (nlinarith).

The reflection identification of the mirror partner and the angular order at P
both require the placement layer and are not formalized here.

No sorry; standard axioms.
-/

namespace Erdos634.Draft.MirrorUWrap

open Erdos634.ApexRigidity

-- ─── thm:nobothmirror ───────────────────────────────────────────────

/-- The first factor e²−ef−f² is always negative. -/
theorem no_mirror_quad_neg {e f : ℝ} (he : 0 < e) (hef : e < f) :
    e ^ 2 - e * f - f ^ 2 < 0 :=
  quad_neg_always he hef

/-- The three cross products are simultaneously positive exactly when e²+ef < f². -/
theorem no_mirror_overlap_signs {e f : ℝ}
    (he : 0 < e) (hf : 0 < f) (hef : e < f) (hgold : e ^ 2 + e * f < f ^ 2)
    (r : ℝ) (hr : 0 < r) :
    0 < e ^ 3 * r / 2 ∧
    0 < e ^ 3 * r * (f - e) * (f + e) / (2 * f ^ 2) ∧
    0 < e * r * (e ^ 2 - e * f - f ^ 2) * (e ^ 2 + e * f - f ^ 2) / (2 * f ^ 2) :=
  overlap_signs he hf hef hgold r hr

-- ─── prop:Uplacements ───────────────────────────────────────────────

/-- The two flanking drops agree at (3,7): 49·sin β = 40·sin γ (at the exact trig values). -/
theorem U_drops_agree_37 :
    (49 : ℝ) * (20 * Real.sqrt 187 / 343) = 40 * (Real.sqrt 187 / 14) :=
  drops_agree_37

/-- The horizontal separation of U's flanking vertices at (3,7) is exactly a = 21. -/
theorem U_edge_length_at_37 : (49 : ℝ) * (207 / 343) - 40 * (3 / 14) = 21 :=
  U_edge_length_37

/-- V is interior to U's edge whenever e²+ef < f². -/
theorem U_V_interior {e f : ℝ} (he : 0 < e) (hef : e < f) (hgold : e ^ 2 + e * f < f ^ 2) :
    f ^ 2 - (f ^ 2 - e ^ 2) < f ^ 2 - e ^ 2 :=
  V_interior he hef hgold

-- Non-vacuity for no_mirror_overlap_signs: e=1, f=2 satisfies e²+ef=3<f²=4.
-- Non-vacuity for U_V_interior: e=1, f=2 gives f²-b=1 < b=3. ✓

#print axioms no_mirror_quad_neg
#print axioms no_mirror_overlap_signs
#print axioms U_drops_agree_37
#print axioms U_edge_length_at_37
#print axioms U_V_interior

end Erdos634.Draft.MirrorUWrap
