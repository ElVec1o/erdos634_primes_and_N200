import Erdos634.CollarAreaM4

/-!
# Area-determinant lemmas for the M=4 collar

Re-exports results of `CollarAreaM4`:
- `apex_area_sum`: area sum over the translated apex tiling equals the target area.
- `column_area_sum`: area sum over the translated/scaled column tiling equals 4× the pgram area.

No `sorry`.
-/

namespace Erdos634.Draft.CollarAreaM4Wrap

open Erdos634.Geometry Erdos634.CertCoord Erdos634.DissectionMap Erdos634.AreaDet
open Erdos634.Realizable Erdos634.TranslateDissection Erdos634.Z15Real

/-- Wrap: `edgeMap` of `mapTri e T` equals the linear composition. -/
theorem edgeMap_mapTri_wrap (e : Plane ≃ᵃ[ℝ] Plane) (T : Tri) :
    edgeMap (mapTri e T) = (e.linear : Plane →ₗ[ℝ] Plane).comp (edgeMap T) :=
  edgeMap_mapTri e T

/-- Wrap: `detTri` scales by the linear determinant of an affine equiv. -/
theorem detTri_mapTri_wrap (e : Plane ≃ᵃ[ℝ] Plane) (T : Tri) :
    detTri (mapTri e T) = LinearMap.det (e.linear : Plane →ₗ[ℝ] Plane) * detTri T :=
  detTri_mapTri e T

/-- Wrap: apex area sum at translation `v` equals the target triangle's area. -/
theorem apex_area_sum_wrap (v : Plane) :
    ∑ i : Fin Tiling44.tiles.length,
        |detTri (mapTri (transEquiv v).toAffineEquiv (Erdos634.Tiling44Bridge.pieceAt i))|
      = |detTri Erdos634.Tiling44Bridge.targetTri| :=
  apex_area_sum v

/-- Wrap: column area sum at translation `w` equals 4× the pgram target area. -/
theorem column_area_sum_wrap (w : Plane) :
    ∑ i : Fin PgramTiling22.tiles.length,
        |detTri (mapTri (transEquiv w).toAffineEquiv
          (mapTri (homothetyEquiv (mkPt 0 0) 2 (by norm_num))
            (Erdos634.PgramTiling22Bridge.pieceAt i)))|
      = 4 * |toR PgramTiling22.area2target| :=
  column_area_sum w

example : True := trivial

#print axioms apex_area_sum_wrap
#print axioms column_area_sum_wrap

end Erdos634.Draft.CollarAreaM4Wrap
