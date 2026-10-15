-- Draft/FDC63.lean -- the 63-tiling with the exact side assignment.
--
-- `CevianTiling63Bridge.model_sides` exports only a per-side disjunction over {256,576,1024}
-- (it does not exclude an equilateral model).  Here: (1) the exact squared sides of
-- `dissection.model` at the pairs 01, 12, 20 are 576, 256, 1024 (so 24, 16, 32 = 8*(3,2,4)), and
-- those of `dissection.target` are 28224, 36864, 20736 (168, 192, 144 = 8*(21,24,18));
-- (2) the paper's own scale: after the 1/8 homothety (`Realizable.scaleDissection`) there is a
-- `CongruentDissection 63` whose target has sides (21,24,18) and whose model has sides (2,3,4)
-- (`HasSides`, any vertex order, as in `FDBBaseBetaE1`).
-- Imported by `All`.  No sorry, no native_decide.
import Erdos634.CevianTiling63Bridge
import Erdos634.Draft.FDBBaseBetaE1

namespace Erdos634.Draft.FDC63
open Erdos634.Z15Real Erdos634.Geometry Erdos634.CevianTiling63Bridge
open Erdos634.Draft.FDBBaseBetaE1 (HasSides tau3)

/-- **The exact squared sides of the model tile of `CevianTiling63Bridge.dissection`**:
pair `01` is `576 = 24^2`, pair `12` is `256 = 16^2`, pair `20` is `1024 = 32^2`. -/
theorem model_sides_exact :
    dist (dissection.model.pts 0) (dissection.model.pts 1) ^ 2 = 576 ∧
    dist (dissection.model.pts 1) (dissection.model.pts 2) ^ 2 = 256 ∧
    dist (dissection.model.pts 2) (dissection.model.pts 0) ^ 2 = 1024 := by
  have e01 : CevianTiling63.dist2 (vertexOf CevianTiling63.tiles.headI 0) (vertexOf CevianTiling63.tiles.headI 1)
      = ((576:ℤ),(0:ℤ)) := by decide
  have e12 : CevianTiling63.dist2 (vertexOf CevianTiling63.tiles.headI 1) (vertexOf CevianTiling63.tiles.headI 2)
      = ((256:ℤ),(0:ℤ)) := by decide
  have e20 : CevianTiling63.dist2 (vertexOf CevianTiling63.tiles.headI 2) (vertexOf CevianTiling63.tiles.headI 0)
      = ((1024:ℤ),(0:ℤ)) := by decide
  have hm : dissection.model = pieceTri headI_mem_tiles := rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [hm, pieceTri_dist_sq _ headI_mem_tiles 0 1, e01]; simp [toR]
  · rw [hm, pieceTri_dist_sq _ headI_mem_tiles 1 2, e12]; simp [toR]
  · rw [hm, pieceTri_dist_sq _ headI_mem_tiles 2 0, e20]; simp [toR]

/-- The same, as lengths: `24, 16, 32` (the tile `(2,3,4)` at scale 8, sides in the order
`3, 2, 4` at the pairs `01, 12, 20`). -/
theorem model_dists_exact :
    dist (dissection.model.pts 0) (dissection.model.pts 1) = 24 ∧
    dist (dissection.model.pts 1) (dissection.model.pts 2) = 16 ∧
    dist (dissection.model.pts 2) (dissection.model.pts 0) = 32 := by
  obtain ⟨h1, h2, h3⟩ := model_sides_exact
  refine ⟨?_, ?_, ?_⟩
  · exact (sq_eq_sq₀ dist_nonneg (by norm_num)).mp (by rw [h1]; norm_num)
  · exact (sq_eq_sq₀ dist_nonneg (by norm_num)).mp (by rw [h2]; norm_num)
  · exact (sq_eq_sq₀ dist_nonneg (by norm_num)).mp (by rw [h3]; norm_num)

/-- The target of `dissection`, exactly: `168, 192, 144 = 8*(21,24,18)` at the pairs `01, 12, 20`. -/
theorem target_dists_exact :
    dist (dissection.target.pts 0) (dissection.target.pts 1) = 168 ∧
    dist (dissection.target.pts 1) (dissection.target.pts 2) = 192 ∧
    dist (dissection.target.pts 2) (dissection.target.pts 0) = 144 := by
  obtain ⟨h1, h2, h3⟩ := targetTri_sides
  have ht : dissection.target = targetTri := rfl
  rw [ht]
  refine ⟨?_, ?_, ?_⟩
  · exact (sq_eq_sq₀ dist_nonneg (by norm_num)).mp (by rw [h1]; norm_num)
  · exact (sq_eq_sq₀ dist_nonneg (by norm_num)).mp (by rw [h2]; norm_num)
  · exact (sq_eq_sq₀ dist_nonneg (by norm_num)).mp (by rw [h3]; norm_num)

/-- The model's vertex order for `HasSides _ 2 3 4`: `0 ↦ 0, 1 ↦ 2, 2 ↦ 1`. -/
def tauM : Equiv.Perm (Fin 3) := ⟨![0, 2, 1], ![0, 2, 1], by decide, by decide⟩

/-- `thm:63` at the certificate's own count `tiles.length` (which is `63`, `tiles_length_eq_63`). -/
theorem thm63_scaled :
    ∃ D : CongruentDissection CevianTiling63.tiles.length,
      HasSides D.target 21 24 18 ∧ HasSides D.model 2 3 4 := by
  have hr : (1 / 8 : ℝ) ≠ 0 := by norm_num
  obtain ⟨t01, t12, t20⟩ := target_dists_exact
  obtain ⟨m01, m12, m20⟩ := model_dists_exact
  refine ⟨Erdos634.Realizable.scaleDissection (0 : Plane) (1 / 8) hr dissection,
    ⟨tau3, ?_, ?_, ?_⟩, ⟨tauM, ?_, ?_, ?_⟩⟩
  · have e1 : tau3 1 = 0 := rfl
    have e2 : tau3 2 = 1 := rfl
    rw [e1, e2, Erdos634.Realizable.scaleDissection_target_pts,
      Erdos634.Realizable.scaleDissection_target_pts, Erdos634.Realizable.homothetyEquiv_dist, t01]
    norm_num [abs_of_pos]
  · have e2 : tau3 2 = 1 := rfl
    have e0 : tau3 0 = 2 := rfl
    rw [e2, e0, Erdos634.Realizable.scaleDissection_target_pts,
      Erdos634.Realizable.scaleDissection_target_pts, Erdos634.Realizable.homothetyEquiv_dist, t12]
    norm_num [abs_of_pos]
  · have e0 : tau3 0 = 2 := rfl
    have e1 : tau3 1 = 0 := rfl
    rw [e0, e1, Erdos634.Realizable.scaleDissection_target_pts,
      Erdos634.Realizable.scaleDissection_target_pts, Erdos634.Realizable.homothetyEquiv_dist, t20]
    norm_num [abs_of_pos]
  · have e1 : tauM 1 = 2 := rfl
    have e2 : tauM 2 = 1 := rfl
    rw [e1, e2, Erdos634.Realizable.scaleDissection_model_pts,
      Erdos634.Realizable.scaleDissection_model_pts, Erdos634.Realizable.homothetyEquiv_dist,
      dist_comm, m12]
    norm_num [abs_of_pos]
  · have e2 : tauM 2 = 1 := rfl
    have e0 : tauM 0 = 0 := rfl
    rw [e2, e0, Erdos634.Realizable.scaleDissection_model_pts,
      Erdos634.Realizable.scaleDissection_model_pts, Erdos634.Realizable.homothetyEquiv_dist,
      dist_comm, m01]
    norm_num [abs_of_pos]
  · have e0 : tauM 0 = 0 := rfl
    have e1 : tauM 1 = 2 := rfl
    rw [e0, e1, Erdos634.Realizable.scaleDissection_model_pts,
      Erdos634.Realizable.scaleDissection_model_pts, Erdos634.Realizable.homothetyEquiv_dist,
      dist_comm, m20]
    norm_num [abs_of_pos]

/-- **The 63-tiling, as written:** there is a dissection of the triangle with sides
`(21,24,18)` into exactly `63` copies of the triangle `(2,3,4)` (every tile congruent to the model,
whose sides are `(2,3,4)`).  `HasSides T a b c`: the sides of `T` are `a, b, c` in some vertex
order, so no labelling or orientation convention enters.  The target's angles
`(beta, 2alpha, alpha+beta)` follow from the side lengths (law of cosines) and are not restated. -/
theorem thm63_paper :
    ∃ D : CongruentDissection 63, HasSides D.target 21 24 18 ∧ HasSides D.model 2 3 4 := by
  have h := thm63_scaled
  rw [tiles_length_eq_63] at h
  exact h

/-- Second clause of `thm:63`, "consequently `63 m^2` is a tile count for every `m >= 1`": already
`CevianTiling63Bridge.exists_dissection_63_mul_sq` (same tile; target the `m`-fold enlargement). -/
theorem thm63_consequence (m : ℕ) (hm : 0 < m) :
    ∃ E : CongruentDissection (63 * m ^ 2), E.model = dissection.model :=
  exists_dissection_63_mul_sq m hm

end Erdos634.Draft.FDC63

#print axioms Erdos634.Draft.FDC63.model_sides_exact
#print axioms Erdos634.Draft.FDC63.model_dists_exact
#print axioms Erdos634.Draft.FDC63.target_dists_exact
#print axioms Erdos634.Draft.FDC63.thm63_paper
#print axioms Erdos634.Draft.FDC63.thm63_consequence
