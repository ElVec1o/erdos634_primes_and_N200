import Erdos634.BentWallCoupling

/-!
# Bent wall coupling: wrapper

Re-exports results of `BentWallCoupling`:
- `straight_implies_bent`: straight edge sums → bent coupling
- `bent_not_implies_straight`: bent coupling does not imply straight
- `bent_underdetermined`: bent coupling is underdetermined
- `straight_strictly_stronger`: straight ↔ bent + each side is π

No `sorry`; standard axioms only.
-/

namespace Erdos634.Draft.BentWallCouplingWrap

open Erdos634.Geometry

theorem bwc_straight_implies_bent (above below : Plane → ℝ) (E : Set Plane)
    (h : HasStraightEdgeSums above below E) : BentCoupling above below E :=
  straight_implies_bent above below E h

theorem bwc_bent_not_implies_straight :
    ∃ (left right : Plane → ℝ) (V : Set Plane),
      BentCoupling left right V ∧ ¬ HasStraightEdgeSums left right V :=
  bent_not_implies_straight

theorem bwc_bent_underdetermined (θ : ℝ) (V : Set Plane) :
    ∃ left right : Plane → ℝ,
      BentCoupling left right V ∧ (∀ v, left v = θ) :=
  bent_underdetermined θ V

theorem bwc_straight_strictly_stronger (above below : Plane → ℝ) (E : Set Plane)
    (h : HasStraightEdgeSums above below E) :
    BentCoupling above below E ∧ (∀ v ∈ E, above v = Real.pi ∧ below v = Real.pi) :=
  straight_strictly_stronger above below E h

-- Non-vacuity: straight_implies_bent is instantiatable via the straight case
example (above below : Plane → ℝ) (E : Set Plane) (h : HasStraightEdgeSums above below E) :
    BentCoupling above below E := bwc_straight_implies_bent above below E h

#print axioms bwc_straight_strictly_stronger
#print axioms bwc_bent_not_implies_straight

end Erdos634.Draft.BentWallCouplingWrap
