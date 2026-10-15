import Erdos634.DissectionMap

/-!
# DissectionMap: affine transport of dissections, wrapper

Key results:
- `mapTri_carrier`: image of a tile under affine equiv
- `mapDissection_target/tile`: transported dissection fields
- `mapTri_interiors_disjoint`: affine equiv preserves interior disjointness
- `mapTri_mapTri_interiors_disjoint`: composition preserves interior disjointness

No sorry, standard axioms.
-/

namespace Erdos634.Draft.DissectionMapWrap

open Erdos634.DissectionMap Erdos634.Geometry

theorem dm_mapTri_carrier (e : Plane ≃ᵃ[ℝ] Plane) (T : Tri) :
    (mapTri e T).carrier = e '' T.carrier :=
  mapTri_carrier e T

theorem dm_mapDissection_target {N : ℕ} (e : Plane ≃ᵃ[ℝ] Plane) (D : Dissection N) :
    (mapDissection e D).target = mapTri e D.target :=
  mapDissection_target e D

theorem dm_mapDissection_tile {N : ℕ} (e : Plane ≃ᵃ[ℝ] Plane) (D : Dissection N) (i : Fin N) :
    (mapDissection e D).tile i = mapTri e (D.tile i) :=
  mapDissection_tile e D i

theorem dm_mapTri_interiors_disjoint {T U : Tri} (e : Plane ≃ᵃ[ℝ] Plane)
    (h : Disjoint (interior T.carrier) (interior U.carrier)) :
    Disjoint (interior (mapTri e T).carrier) (interior (mapTri e U).carrier) :=
  mapTri_interiors_disjoint e h

theorem dm_mapTri_mapTri_interiors_disjoint {T U : Tri} (e f : Plane ≃ᵃ[ℝ] Plane)
    (h : Disjoint (interior T.carrier) (interior U.carrier)) :
    Disjoint (interior (mapTri f (mapTri e T)).carrier)
      (interior (mapTri f (mapTri e U)).carrier) :=
  mapTri_mapTri_interiors_disjoint e f h

-- Non-vacuity: mapDissection_target is definitional
example {N : ℕ} (e : Plane ≃ᵃ[ℝ] Plane) (D : Dissection N) :
    (mapDissection e D).target = mapTri e D.target :=
  dm_mapDissection_target e D

#print axioms dm_mapTri_carrier
#print axioms dm_mapTri_interiors_disjoint

end Erdos634.Draft.DissectionMapWrap
