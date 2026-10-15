import Erdos634.PentagonLemma

/-!
# The middle region of the `(0,e,2e)` walk: arithmetic core, both stubs

The middle region of the `(0,e,2e)` walk admits no tiling; this file contains the arithmetic of the stubs.

`Pentagon.no_partition` and `pentagon_stub_kills` cover the first-stub arithmetic. This file wraps the FULL two-stub
generalization from `PentagonLemma.lean`:

`pentagon_region_dies` (Lean, `PentagonLemma.lean:206`): for every coprime `1 ≤ e < f` and
tile edge lengths `a = ef`, `b = f²−e²`, `c = f²`, if `t` is either stub produced by a corner
decomposition at the pentagon (`t = e²%b`, `a+t = b`, or `b+t = a`), then:
  (1) `t > 0` (the stub is nonempty), and
  (2) `t` is NOT partitionable into whole tile edges `a,b,c` (the stub kills the region).

Consequence: no corner decomposition can complete — the middle region of the (0,e,2e) walk admits
no whole-edge tiling by {a,b,c}-length boundary segments.

Connecting this to a `RegionDissection` object requires proving that the
pentagon region's actual boundary decomposition produces one of these three stub forms, a step
that uses the walk/placement structure of the `(0,e,2e)` approach along the hypotenuse; that
geometric step is not part of this file.

Axioms at most [propext, Classical.choice, Quot.sound]; no `sorry`.
-/

namespace Erdos634.Draft.PentagonWrap

open Erdos634.PentagonLemma

/-- Both stubs from a corner decomposition at the pentagon are positive and not partitionable. -/
theorem pentagon_stub_kills_both {e f a b c t : ℕ}
    (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f)
    (ha : a = e * f) (hb : b + e * e = f * f) (hc : c = f * f)
    (hstub : t = e * e % b ∨ a + t = b ∨ b + t = a) :
    0 < t ∧ ¬ Partitionable a b c t :=
  pentagon_region_dies hco he hef ha hb hc hstub

/-- The unique whole-edge partition of `b` itself is `(0,1,0)` — the single `b`-partner. -/
theorem pentagon_partner_unique {e f a b c : ℕ}
    (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f)
    (ha : a = e * f) (hb : b + e * e = f * f) (hc : c = f * f)
    {x y z : ℕ} (h : x * a + y * b + z * c = b) : x = 0 ∧ y = 1 ∧ z = 0 :=
  partner_unique hco he hef ha hb hc h

/-- Non-vacuity: the hypotheses are satisfiable. At (e,f) = (1,2): a=2, b=3, c=4, and
e²%b = 1 is the first stub (positive and not partitionable into {2,3,4}). -/
theorem pentagon_witness :
    let e := 1; let f := 2; let a := e * f; let b := f * f - e * e
    let t := (e * e) % b
    Nat.Coprime e f ∧ 1 ≤ e ∧ e < f ∧ (t = e * e % b ∨ a + t = b ∨ b + t = a) := by
  decide

#print axioms pentagon_stub_kills_both
#print axioms pentagon_partner_unique

end Erdos634.Draft.PentagonWrap
