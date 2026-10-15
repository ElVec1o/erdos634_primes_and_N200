/-
Draft/BaseBetaScale2.lean -- the base-β targets at scale two have no tiling for the members with `f ≤ 4`, `f ≥ 3`.

For coprime `1 ≤ e < f` the base-β target of the tile `(ef, f² − e², f²)` at scale `M` is the isosceles triangle with
legs `M f³` and base `M e (3f² − e²)`.  Four kernel-checked certificates refute the scale-two targets of the
members `(1,3)`, `(2,3)`, `(1,4)`, `(3,4)` (they are instances of `N = 104, 92, 188, 156`); this file states the
four facts in one form and together:

    theorem basebeta_scale_two {e f : ℕ} (h : (e = 1 ∧ f = 3) ∨ (e = 2 ∧ f = 3) ∨ (e = 1 ∧ f = 4) ∨ (e = 3 ∧ f = 4))
        {N : ℕ} (D : CongruentDissection N) :
        ¬ (HasSides D.target (2 f³) (2 f³) (2 e (3 f² − e²)) ∧ HasSides D.model (e f) (f² − e²) (f²))

(`HasSides T a b c`: the sides of `T` are `a, b, c` in some labelling; `N` is arbitrary, reflections are allowed.)
`scale_two_1_2_exists`: for the member `(1,2)` the scale-two target `(16,16,22)` HAS a tiling (44 tiles), so the
hypothesis on `(e,f)` cannot be dropped.

Context (not proved here): D. Paliy announces tilings of the base-β target of every member at every scale `M ≥ f`.
Whether the scales `2 ≤ M < f` are always empty is open.

Certificates: `Refl.MNU104` (56,016 nodes), `Refl.MS1N92` (31,709), `Refl.MS1N188` (56,629), `Refl.MS1N156`
(234,239).  Imports the large certificate of `156`: built in `AllCert1`, not in `All`.
No sorry, no native_decide.
-/
import Erdos634.Draft.NotUniform104
import Erdos634.Draft.N92
import Erdos634.Draft.N188
import Erdos634.Draft.N156Final

namespace Erdos634.Draft.BaseBetaScale2

open Erdos634.Geometry Erdos634.CertNode Erdos634.CertCoord Erdos634.Draft.FDBBaseBetaE1

/-- member `(1,3)`: tile `(3,8,9)`, legs `54`, base `52` -/
theorem scale_two_1_3 {N : ℕ} (D : CongruentDissection N) :
    ¬ (HasSides D.target 54 54 52 ∧ HasSides D.model 3 8 9) :=
  Erdos634.Draft.NotUniform104.notuniform_104 D

/-- member `(2,3)`: tile `(6,5,9)`, legs `54`, base `92` -/
theorem scale_two_2_3 {N : ℕ} (D : CongruentDissection N) :
    ¬ (HasSides D.target 54 54 92 ∧ HasSides D.model 6 5 9) := by
  rintro ⟨hT, hM⟩
  obtain ⟨g1, g2, g3⟩ := Erdos634.Draft.N92.TGT_S1N92
  obtain ⟨k1, k2, k3⟩ := Refl.MS1N92.MODEL_sides
  exact Refl.MS1N92.not_dissection D (congruent_of_hasSides' (hasSides_rot (hasSides_rot hT)) g1 g2 g3)
    (congruent_of_hasSides' (hasSides_rot hM) k1 k2 k3)

/-- member `(1,4)`: tile `(4,15,16)`, legs `128`, base `94` -/
theorem scale_two_1_4 {N : ℕ} (D : CongruentDissection N) :
    ¬ (HasSides D.target 128 128 94 ∧ HasSides D.model 4 15 16) := by
  rintro ⟨hT, hM⟩
  obtain ⟨g1, g2, g3⟩ := Erdos634.Draft.N188.TGT_S1
  obtain ⟨k1, k2, k3⟩ := Refl.MS1N188.MODEL_sides
  exact Refl.MS1N188.not_dissection D (congruent_of_hasSides' hT g1 g2 g3)
    (congruent_of_hasSides' (hasSides_rot hM) k1 k2 k3)

/-- member `(3,4)`: tile `(12,7,16)`, legs `128`, base `234` -/
theorem scale_two_3_4 {N : ℕ} (D : CongruentDissection N) :
    ¬ (HasSides D.target 128 128 234 ∧ HasSides D.model 12 7 16) := by
  rintro ⟨hT, hM⟩
  obtain ⟨g1, g2, g3⟩ := Erdos634.Draft.N156.TGT_S1N156
  obtain ⟨k1, k2, k3⟩ := Refl.MS1N156.MODEL_sides
  exact Refl.MS1N156.not_dissection D (congruent_of_hasSides' (hasSides_rot (hasSides_rot hT)) g1 g2 g3)
    (congruent_of_hasSides' (hasSides_rot hM) k1 k2 k3)

/-- **The base-β targets at scale two, `3 ≤ f ≤ 4`**: no dissection, into any number of tiles. -/
theorem basebeta_scale_two {e f : ℕ}
    (h : (e = 1 ∧ f = 3) ∨ (e = 2 ∧ f = 3) ∨ (e = 1 ∧ f = 4) ∨ (e = 3 ∧ f = 4))
    {N : ℕ} (D : CongruentDissection N) :
    ¬ (HasSides D.target (2 * (f : ℝ) ^ 3) (2 * (f : ℝ) ^ 3) (2 * (e : ℝ) * (3 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2)) ∧
      HasSides D.model ((e : ℝ) * f) ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ((f : ℝ) ^ 2)) := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rintro ⟨hT, hM⟩
    norm_num at hT hM
    exact scale_two_1_3 D ⟨hT, hM⟩
  · rintro ⟨hT, hM⟩
    norm_num at hT hM
    exact scale_two_2_3 D ⟨hT, hM⟩
  · rintro ⟨hT, hM⟩
    norm_num at hT hM
    exact scale_two_1_4 D ⟨hT, hM⟩
  · rintro ⟨hT, hM⟩
    norm_num at hT hM
    exact scale_two_3_4 D ⟨hT, hM⟩

/-- for the member `(1,2)` the scale-two target has a tiling (`44` tiles): the restriction on `(e,f)` is needed -/
theorem scale_two_1_2_exists :
    ∃ D : CongruentDissection 44, HasSides D.target 16 16 22 ∧ HasSides D.model 2 3 4 :=
  Erdos634.Draft.NotUniform104.thm_notuniform.1

end Erdos634.Draft.BaseBetaScale2

#print axioms Erdos634.Draft.BaseBetaScale2.basebeta_scale_two
#print axioms Erdos634.Draft.BaseBetaScale2.scale_two_1_2_exists
