import Erdos634.Refl.MNU104Sound
import Erdos634.Draft.HasSidesPerm

/-!
# The base-β family is not uniform

For the member `(e,f) = (1,3)` -- tile `(3,8,9)`, `N₁ = 26` -- the scale-2 target
admits no tiling: `N = 104` is not realized.  Hence the existence of `Δ₂` for `(1,2)` does not extend along the
family: `Δ₂` exists for `(1,2)` and does not exist for `(1,3)`.

The scale-2 base-β target of `(1,3)` is the isosceles triangle with legs `2·3³ = 54` and base `2·1·(3·9−1) = 52`.
`notuniform_104`: no `CongruentDissection` (any number of tiles, reflections allowed) of a triangle with sides
`(54, 54, 52)` by a tile with sides `(3, 8, 9)`.  `thm_notuniform` adds the existence half from
`FDBBaseBetaE1.thm_realize12` (`Δ₂` of `(1,2)`: sides `(16,16,22)`, tile `(2,3,4)`, 44 tiles).

Certificate: `Refl.MNU104.not_dissection` (56,016 nodes, `CheckN` with nogoods).  No sorry, no native_decide.
-/

open Erdos634.CertNode Erdos634.Geometry Erdos634.CertCoord

namespace Erdos634.Draft.NotUniform104

open Erdos634.Draft.FDBBaseBetaE1

theorem TGT_sides : dist (Refl.MNU104.TGT.pts 0) (Refl.MNU104.TGT.pts 1) = 52 ∧
    dist (Refl.MNU104.TGT.pts 1) (Refl.MNU104.TGT.pts 2) = 54 ∧
    dist (Refl.MNU104.TGT.pts 0) (Refl.MNU104.TGT.pts 2) = 54 :=
  model_sides_rp Refl.MNU104.hDn Refl.MNU104.TGT_pos (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

/-- **The scale-2 target of `(1,3)` admits no tiling.** -/
theorem notuniform_104 {N : ℕ} (D : CongruentDissection N) :
    ¬ (HasSides D.target 54 54 52 ∧ HasSides D.model 3 8 9) := by
  rintro ⟨hT, hM⟩
  obtain ⟨g1, g2, g3⟩ := TGT_sides
  obtain ⟨k1, k2, k3⟩ := Refl.MNU104.MODEL_sides
  have hTc : D.target.Congruent Refl.MNU104.TGT := congruent_of_hasSides' hT g1 g2 g3
  have hMc : D.model.Congruent Refl.MNU104.MODEL := congruent_of_hasSides' (hasSides_rot hM) k1 k2 k3
  exact Refl.MNU104.not_dissection D hTc hMc

/-- **`thm:notuniform`**: `Δ₂` exists for the member `(1,2)` and does not exist for `(1,3)`. -/
theorem thm_notuniform :
    (∃ D : CongruentDissection 44, HasSides D.target 16 16 22 ∧ HasSides D.model 2 3 4) ∧
    (∀ (N : ℕ) (D : CongruentDissection N), ¬ (HasSides D.target 54 54 52 ∧ HasSides D.model 3 8 9)) := by
  refine ⟨?_, fun N D => notuniform_104 D⟩
  obtain ⟨D, h1, h2⟩ := (thm_realize12 2 (by norm_num)).1 (by norm_num)
  refine ⟨D, ?_, h2⟩
  convert h1 using 1 <;> norm_num

end Erdos634.Draft.NotUniform104

#print axioms Erdos634.Draft.NotUniform104.thm_notuniform
