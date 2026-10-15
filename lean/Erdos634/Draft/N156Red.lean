/-
Draft/N156Red.lean -- `156` reduced to ONE instance.

`156 = 4 · 39` is not decided here.  Of the three instances of `OpenRed.not_tile_156_of`, two are now closed by
kernel-checked certificates:

* S5 `(t, e, f) = (2, 5, 8)`: tile `(40, 39, 64)` on the isosceles triangle with base `390` and legs `624`
  (`Refl.MS156.not_dissection`, 70,504 nodes): `s5inst_2_5_8`;
* the `γ = 2α` pair `(6, 26)`: tile `(25, 39, 40)` on `(390, 390, 624)` (`Refl.MG156.not_dissection`, 87,352 nodes):
  `GPairs156.gpair_6_26`.

What is left is the base-β instance, the member `(3, 4)` at scale `2`:

    theorem not_tile_156_of_s1 (h : S1Inst 2 3 4) (D : CongruentDissection 156) : False

(the tile `(12, 7, 16)` on the isosceles triangle with legs `128` and base `234`).

Composite-N work; not prime-case work.  No sorry, no native_decide.
-/
import Erdos634.Draft.OpenReductionsNsq
import Erdos634.Draft.GPairs156
import Erdos634.Refl.MS156Sound

open scoped Classical
set_option maxRecDepth 8000
set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000

namespace Erdos634.Draft.N156

open Erdos634.Geometry Erdos634.Draft.NSQM Erdos634.CertNode Erdos634.CertCoord Erdos634.Draft.OpenRed
open Erdos634.Draft.FDBBaseBetaE1 Erdos634.Draft.GPairCert Erdos634.Draft.TileCountFamilies
open Erdos634.Draft.CompositeFinal4

theorem TGT_S156 : dist (Refl.MS156.TGT.pts 0) (Refl.MS156.TGT.pts 1) = 390 ∧
    dist (Refl.MS156.TGT.pts 1) (Refl.MS156.TGT.pts 2) = 624 ∧ dist (Refl.MS156.TGT.pts 0) (Refl.MS156.TGT.pts 2) = 624 :=
  model_sides_rp Refl.MS156.hDn Refl.MS156.TGT_pos (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

/-- S5 `(t,e,f) = (2,5,8)`: tile `(40,39,64)`, target `(390,624,624)`. -/
theorem s5inst_2_5_8 : S5Inst 2 5 8 :=
  s5inst_of_cert 2 5 8 Refl.MS156.TGT Refl.MS156.MODEL
    ⟨by rw [TGT_S156.1]; norm_num, by rw [TGT_S156.2.1]; norm_num, by rw [TGT_S156.2.2]; norm_num⟩
    ⟨by rw [Refl.MS156.MODEL_sides.1]; norm_num, by rw [Refl.MS156.MODEL_sides.2.1]; norm_num,
      by rw [Refl.MS156.MODEL_sides.2.2]; norm_num⟩
    (fun D hT hM => Refl.MS156.not_dissection D hT hM)

/-- **`156` from its one open instance**: if the tile `(12, 7, 16)` does not tile the isosceles triangle with legs
`128` and base `234` (the base-β member `(3, 4)` at scale `2`), then `156` is not a tile count. -/
theorem not_tile_156_of_s1 (h : S1Inst 2 3 4) (D : CongruentDissection 156) : False :=
  not_tile_156_of h (@s5inst_2_5_8) Erdos634.Draft.GPairs156.gpair_6_26 D

theorem not_tileCount_156_of_s1 (h : S1Inst 2 3 4) : ¬ TileCount 156 :=
  fun ⟨D⟩ => not_tile_156_of_s1 h D

end Erdos634.Draft.N156

#print axioms Erdos634.Draft.N156.not_tile_156_of_s1
