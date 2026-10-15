/-
Draft/N120.lean -- `N = 120` is NOT a tile count.

`120 = 30 · 2²`.  Beyond the arithmetic leaves (`Draft/N120Arith.lean`) three leaves remain:
* tiles with all angles in `ℚπ`: `GAUFinal.gapA_120` (the uniform theorem for `N = 30 s²`);
* a tile with an angle `π/3` on the equilateral triangle: `E60N120.gapE60_120` (the pair `(60, 6)` has a non-square
  discriminant, `E60Irr.e60Pair_of_not_isSquare`; the pair `(36, 10)`, tile `(8, 13, 15)`, has the certificate
  `Refl.MP120x36.not_dissection`, 65,710 nodes);
* the `F₁` pair `(6, 20)`: tile `(7, 8, 13)` on the target `(56, 104, 120)`, certificate
  `Refl.MF120.not_dissection` (88,484 nodes).

Composite-N result.  NOT prime-case work.  No sorry, no native_decide.
-/
import Erdos634.Draft.N120Arith
import Erdos634.Draft.GAUFinal
import Erdos634.Draft.E60N120
import Erdos634.Refl.MF120Sound

open scoped Classical

namespace Erdos634.Draft.N120

open Erdos634.Geometry Erdos634.Draft.FDBBaseBetaE1 Erdos634.Draft.F1PairCert Erdos634.CertNode Erdos634.CertCoord

theorem TGT_F : dist (Refl.MF120.TGT.pts 0) (Refl.MF120.TGT.pts 1) = 120 ∧
    dist (Refl.MF120.TGT.pts 1) (Refl.MF120.TGT.pts 2) = 56 ∧
    dist (Refl.MF120.TGT.pts 0) (Refl.MF120.TGT.pts 2) = 104 :=
  model_sides_rp Refl.MF120.hDn Refl.MF120.TGT_pos (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

/-- the pair `(6, 20)`: tile `(7, 8, 13)`, target `(56, 104, 120)` -/
theorem f1pair_6_20 : F1Pair 120 6 20 := by
  obtain ⟨g1, g2, g3⟩ := TGT_F
  obtain ⟨k1, k2, k3⟩ := Refl.MF120.MODEL_sides
  exact f1Pair_of_cert 120 6 20 (by norm_num) 7 8 13 8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) Refl.MF120.TGT Refl.MF120.MODEL
    (fun T h => congruent_of_hasSides' h (by rw [g1]; norm_num) (by rw [g2]; norm_num) (by rw [g3]; norm_num))
    (fun T h => congruent_of_hasSides' (hasSides_rot h) k1 k2 k3)
    (fun D' hT hM => Refl.MF120.not_dissection D' hT hM)

/-- **`120` is not a tile count** (no `CongruentDissection 120` exists). -/
theorem not_tile_120 (D : CongruentDissection 120) : False :=
  not_tile_120_of Erdos634.Draft.GAU.gapA_120 Erdos634.Draft.E60N120.gapE60_120 f1pair_6_20 D

end Erdos634.Draft.N120

#print axioms Erdos634.Draft.N120.not_tile_120
