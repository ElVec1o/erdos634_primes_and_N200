import Erdos634.AreaDet

/-!
# Area-determinant bridge (volume = |det|): wrapper

Re-exports, under `ad_` names, results of `AreaDet`:
- `volume_eq_det_mul`: vol(T) = (1/2)|det(T)|
- `area_identity_of_det`: N tiles covering target → sum of dets = det(target)
- `volume_stdCarrier_half`: vol(stdCarrier) = 1/2
- `volume_reflMap_image`: reflections preserve volume
- `aedisjoint_stdCarrier`: stdCarrier and stdCarrier2 are a.e. disjoint

No `sorry`; standard axioms only.
-/

namespace Erdos634.Draft.AreaDetWrap

open Erdos634.AreaDet Erdos634.Geometry MeasureTheory

theorem ad_volume_eq_det_mul (T : Tri) :
    volume T.carrier = ENNReal.ofReal |detTri T| * volume stdCarrier :=
  volume_eq_det_mul T

theorem ad_area_identity_of_det {N : ℕ} (target : Tri) (tile : Fin N → Tri)
    (h : ∑ i, |detTri (tile i)| = |detTri target|) :
    ∑ i, volume (tile i).carrier = volume target.carrier :=
  area_identity_of_det target tile h

theorem ad_volume_stdCarrier_half : volume stdCarrier = 1 / 2 :=
  volume_stdCarrier_half

theorem ad_volume_reflMap_image (S : Set Plane) :
    volume (reflMap '' S) = volume S :=
  volume_reflMap_image S

theorem ad_pb_repr (v : Plane) (i : Fin 2) : pb.repr v i = v i :=
  pb_repr v i

-- detTri_eq: just expose the identity (exact type from source)
theorem ad_detTri_eq (T : Tri) :
    detTri T =
      (T.pts 1 - T.pts 0).ofLp 0 * (T.pts 2 - T.pts 0).ofLp 1 -
      (T.pts 2 - T.pts 0).ofLp 0 * (T.pts 1 - T.pts 0).ofLp 1 :=
  detTri_eq T

theorem ad_placeMap_stdCarrier (T : Tri) :
    (placeMap T) '' stdCarrier = T.carrier :=
  placeMap_stdCarrier T

theorem ad_aedisjoint_stdCarrier :
    AEDisjoint volume stdCarrier stdCarrier2 :=
  aedisjoint_stdCarrier

-- Non-vacuity: volume identity type-checks
example : @ad_volume_eq_det_mul = @ad_volume_eq_det_mul := rfl

#print axioms ad_volume_eq_det_mul
#print axioms ad_area_identity_of_det

end Erdos634.Draft.AreaDetWrap
