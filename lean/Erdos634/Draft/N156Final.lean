/-
Draft/N156Final.lean -- `N = 156` is NOT a tile count.

`156 = 4 · 39`.  `N156Red.not_tile_156_of_s1` reduced `156` to one instance: the base-β member `(3, 4)` at scale
`2`, tile `(12, 7, 16)` on the isosceles triangle with legs `128` and base `234`.  That instance is closed here by
the kernel-checked certificate `Refl.MS1N156.not_dissection` (exact replay over `ℚ(√55)` of a search tree found
with the target in the orientation leg, base, leg and the order `band:16`).

    theorem not_tile_156 (D : CongruentDissection 156) : False
    theorem not_tileCount_156 : ¬ TileCount 156

The three instances of `156`: S1 `(2,3,4)` (this file), S5 `(2,5,8)` (`N156Red.s5inst_2_5_8`, `Refl.MS156`), the
`γ = 2α` pair `(6,26)` (`GPairs156.gpair_6_26`, `Refl.MG156`).

Composite-N result.  NOT prime-case work.  No sorry, no native_decide.
-/
import Erdos634.Draft.N156Red
import Erdos634.Draft.N92
import Erdos634.Refl.MS1N156Sound

open scoped Classical
set_option maxRecDepth 8000
set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000

namespace Erdos634.Draft.N156

open Erdos634.Geometry Erdos634.Draft.NSQM Erdos634.CertNode Erdos634.CertCoord Erdos634.Draft.OpenRed
open Erdos634.Draft.FDBBaseBetaE1 Erdos634.Draft.GPairCert Erdos634.Draft.TileCountFamilies
open Erdos634.Draft.CompositeFinal4

theorem TGT_S1N156 : dist (Refl.MS1N156.TGT.pts 0) (Refl.MS1N156.TGT.pts 1) = 128 ∧
    dist (Refl.MS1N156.TGT.pts 1) (Refl.MS1N156.TGT.pts 2) = 234 ∧
    dist (Refl.MS1N156.TGT.pts 0) (Refl.MS1N156.TGT.pts 2) = 128 :=
  model_sides_rp Refl.MS1N156.hDn Refl.MS1N156.TGT_pos (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

/-- S1 `(t, p, q) = (2, 3, 4)`: tile `(12, 7, 16)`, target legs `128`, base `234`. -/
theorem s1inst_2_3_4 : S1Inst 2 3 4 :=
  s1inst_of_cert_lbl 2 3 4 Refl.MS1N156.TGT Refl.MS1N156.MODEL
    ⟨by rw [TGT_S1N156.1]; norm_num, by rw [TGT_S1N156.2.1]; norm_num, by rw [TGT_S1N156.2.2]; norm_num⟩
    ⟨by rw [Refl.MS1N156.MODEL_sides.1]; norm_num, by rw [Refl.MS1N156.MODEL_sides.2.1]; norm_num,
      by rw [Refl.MS1N156.MODEL_sides.2.2]; norm_num⟩
    (fun D hT hM => Refl.MS1N156.not_dissection D hT hM)

/-- **`156` is not a tile count.** -/
theorem not_tile_156 (D : CongruentDissection 156) : False :=
  not_tile_156_of_s1 (@s1inst_2_3_4) D

theorem not_tileCount_156 : ¬ TileCount 156 :=
  fun ⟨D⟩ => not_tile_156 D

end Erdos634.Draft.N156

#print axioms Erdos634.Draft.N156.not_tile_156
