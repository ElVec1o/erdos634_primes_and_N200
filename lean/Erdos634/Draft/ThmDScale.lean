import Mathlib.Tactic
import Erdos634.Realizable
import Erdos634.TilePlacement

/-!
Credit: the method (rigidity window, Lemmas 30-34, row induction, Theorem 37) is adapted from M. Beeson and G. Rosu, 'Tiling a triangle into a prime number of congruent triangles' (preprint, 16 Oct 2026); the transfer to the tile with gamma = 2 alpha (fan lemma at straight points, windows u and v, Lemma K) is ours.

# Theorem D' (ThmDGeo): scaling a dissection  

`angle_homothety` (a homothety of positive ratio preserves `cornerAngle`), `sideOpp_scale` (it multiplies `sideOpp` by `|r|`).
-/

namespace Erdos634.Draft.ThmDRun

open Erdos634.Geometry Erdos634.Realizable Erdos634.TilePlacement

theorem angle_homothety (p : Plane) (r : ℝ) (hr : r ≠ 0) (hr0 : 0 < r) (a b c : Plane) :
    cornerAngle (homothetyEquiv p r hr a) (homothetyEquiv p r hr b) (homothetyEquiv p r hr c) = cornerAngle a b c := by
  unfold cornerAngle EuclideanGeometry.angle
  rw [homothetyEquiv_apply, homothetyEquiv_apply, homothetyEquiv_apply]
  have h1 : AffineMap.homothety p r a -ᵥ AffineMap.homothety p r b = r • (a -ᵥ b) := by
    simp only [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add]; module
  have h2 : AffineMap.homothety p r c -ᵥ AffineMap.homothety p r b = r • (c -ᵥ b) := by
    simp only [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add]; module
  rw [h1, h2]
  exact InnerProductGeometry.angle_smul_smul hr _ _

theorem sideOpp_scale (p : Plane) (r : ℝ) (hr : r ≠ 0) (T : Tri) (j : Fin 3) :
    sideOpp (Erdos634.DissectionMap.mapTri (homothetyEquiv p r hr) T) j = |r| * sideOpp T j := by
  unfold sideOpp
  exact homothetyEquiv_dist p r hr _ _

#print axioms angle_homothety
#print axioms sideOpp_scale
end Erdos634.Draft.ThmDRun
