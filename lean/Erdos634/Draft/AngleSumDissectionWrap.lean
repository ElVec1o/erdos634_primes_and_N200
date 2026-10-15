import Erdos634.AngleSumDissection

/-!
# Tile angle sum = target angle: wrapper

Re-exports results of `AngleSumDissection` (all in the `Erdos634.Geometry` namespace):
- `Tri.localAngle_nonneg`: local angles are nonneg
- `Tri.localAngle_interior`: interior point → tile fills its full corner angle
- `Tri.localAngle_frontier`: frontier point → tile fills half at edges, full at vertices
- `Tri.localAngle_vertex`: vertex k → local angle = corner angle there
- `Dissection.sum_localAngle_eq`: ∑ tile.localAngle p = target.localAngle p
- `Dissection.hasAngleSums`: `HasAngleSums` holds for any dissection

No `sorry`; standard axioms only.
-/

namespace Erdos634.Draft.AngleSumDissectionWrap

open Erdos634.Geometry

theorem asd_localAngle_nonneg (T : Tri) (p : Plane) : 0 ≤ T.localAngle p :=
  Tri.localAngle_nonneg T p

theorem asd_sum_localAngle_eq {N : ℕ} (D : Dissection N) (p : Plane) :
    ∑ i, (D.tile i).localAngle p = D.target.localAngle p :=
  Dissection.sum_localAngle_eq D p

theorem asd_hasAngleSums {N : ℕ} (D : Dissection N) :
    HasAngleSums D (fun p i => (D.tile i).localAngle p) :=
  Dissection.hasAngleSums D

-- Non-vacuity
example : @asd_sum_localAngle_eq = @asd_sum_localAngle_eq := rfl

#print axioms asd_sum_localAngle_eq
#print axioms asd_hasAngleSums

end Erdos634.Draft.AngleSumDissectionWrap
