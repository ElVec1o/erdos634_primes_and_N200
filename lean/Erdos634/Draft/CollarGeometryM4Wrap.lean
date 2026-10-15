import Erdos634.CollarGeometryM4

/-!
# Coordinate geometry for the M=4 collar construction

Re-exports results of `CollarGeometryM4`:
- `pgram_scaled_corners`: the 4 corners of the scaled parallelogram.
- `apex_copy_pts`: explicit coordinates of the apex translated tiling target.
- `corner_copy_pts`: explicit coordinates of the corner translated tiling target.
- `piece0_scaled_pts`: coordinates of the scaled piece 0.

No `sorry`.
-/

namespace Erdos634.Draft.CollarGeometryM4Wrap

open Erdos634.Geometry Erdos634.DissectionMap Erdos634.TranslateDissection Erdos634.CertCoord

/-- Wrap: the 4 scaled pgram corners match their explicit coordinates. -/
theorem pgram_scaled_corners_wrap :
    (2:ℝ) • Erdos634.PgramTiling22Bridge.v1 = mkPt 0 0 ∧
    (2:ℝ) • Erdos634.PgramTiling22Bridge.v2 = mkPt 88 0 ∧
    (2:ℝ) • Erdos634.PgramTiling22Bridge.v3 = mkPt 132 (12 * Real.sqrt 15) ∧
    (2:ℝ) • Erdos634.PgramTiling22Bridge.v4 = mkPt 44 (12 * Real.sqrt 15) :=
  pgram_scaled_corners

/-- Wrap: explicit vertex coordinates for the apex translated tiling target. -/
theorem apex_copy_pts_wrap :
    (translateCongruentDissection (mkPt 88 (24 * Real.sqrt 15))
        Erdos634.Tiling44Bridge.dissection).target.pts 0 = mkPt 88 (24 * Real.sqrt 15) ∧
    (translateCongruentDissection (mkPt 88 (24 * Real.sqrt 15))
        Erdos634.Tiling44Bridge.dissection).target.pts 1 = mkPt 264 (24 * Real.sqrt 15) ∧
    (translateCongruentDissection (mkPt 88 (24 * Real.sqrt 15))
        Erdos634.Tiling44Bridge.dissection).target.pts 2 = mkPt 176 (48 * Real.sqrt 15) :=
  apex_copy_pts

/-- Wrap: explicit vertex coordinates for the corner translated tiling target. -/
theorem corner_copy_pts_wrap :
    (translateCongruentDissection (mkPt 176 0)
        Erdos634.Tiling44Bridge.dissection).target.pts 0 = mkPt 176 0 ∧
    (translateCongruentDissection (mkPt 176 0)
        Erdos634.Tiling44Bridge.dissection).target.pts 1 = mkPt 352 0 ∧
    (translateCongruentDissection (mkPt 176 0)
        Erdos634.Tiling44Bridge.dissection).target.pts 2 = mkPt 264 (24 * Real.sqrt 15) :=
  corner_copy_pts

example : True := trivial

#print axioms pgram_scaled_corners_wrap
#print axioms apex_copy_pts_wrap
#print axioms corner_copy_pts_wrap

end Erdos634.Draft.CollarGeometryM4Wrap
