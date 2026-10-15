/-
Draft/Spectrum200Cond2.lean -- the tile-count spectrum up to 200, conditional on nine named instances.

`Spectrum200Cond.tileCount_iff_le_200_of` takes eleven hypotheses (`OpenInstances`).  Two of them are theorems:
`N156.s5inst_2_5_8` (certificate `Refl.MS156`, 70,504 nodes) and `GPairs156.gpair_6_26`
(certificate `Refl.MG156`, 87,352 nodes).  The remaining hypotheses form `OpenInstances9`:

    theorem tileCount_iff_le_200_of9 (h : OpenInstances9) {N : ℕ} (h1 : 1 ≤ N) (h200 : N ≤ 200) :
        TileCount N ↔ FamC N = true

`OpenInstances9` concerns seven values and nine instances.

`OpenInstances9` is false: its field `i143 : F2Inst143` is refuted by the kernel-checked
143-tiling (`Draft.N143.not_f2Inst143`, `Draft.N143.openInstances9_false`), so `tileCount_iff_le_200_of9` is vacuous.
The statement to use is `Draft.N143.tileCount_iff_le_200_of8`.

No sorry, no native_decide.
-/
import Erdos634.Draft.Spectrum200Cond
import Erdos634.Draft.N156Red

namespace Erdos634.Draft.Spectrum200Cond2

open Erdos634.Draft.TileCountFamilies Erdos634.Geometry Erdos634.Draft.FDDSpectrumTable Erdos634.Draft.Spectrum200d
open Erdos634.Draft.Spectrum200g Erdos634.Draft.OpenRed Erdos634.Draft.IsoInst Erdos634.Draft.GapE120Exc
open Erdos634.Draft.CompositeFinal4 Erdos634.Draft.NSQM Erdos634.Draft.NSQRW Erdos634.Draft.GPairCert
open Erdos634.Draft.Spectrum200Cond

/-- **The nine instances on which the spectrum up to 200 depends** (tile, then target):
`132`: `(5,3,7)` on `(42,42,66)`; `135`: the pair `(15,27)` and its mirror, `(3,5,7)` on the equilateral triangle of
side `45`; `143`: `(3,5,7)` on `(39,55,49)`; `154`: `(8,7,13)` on `(91,91,154)`; `156`: `(12,7,16)` on
`(128,128,234)`; `161`: `(12,7,16)` on `(112,112,161)`; `184`: `(7,8,13)` on `(104,104,184)` and `(10,21,25)` on
`(184,210,250)`. -/
structure OpenInstances9 : Prop where
  i132 : IsoInst 5 3 7 6
  i135 : E120Pair 135 15 27
  i135' : E120Pair 135 27 15
  i143 : F2Inst143
  i154 : IsoInst 8 7 13 7
  i156 : S1Inst 2 3 4
  i161 : S3Inst 1 3 4
  i184 : IsoInst 7 8 13 8
  i184' : S4Inst 2 2 5

theorem openInstances_of9 (h : OpenInstances9) : OpenInstances where
  i132 := h.i132
  i135 := h.i135
  i135' := h.i135'
  i143 := h.i143
  i154 := h.i154
  i156 := h.i156
  i156' := @Erdos634.Draft.N156.s5inst_2_5_8
  i156'' := Erdos634.Draft.GPairs156.gpair_6_26
  i161 := h.i161
  i184 := h.i184
  i184' := h.i184'

/-- **The spectrum up to 200, given the nine open instances.** -/
theorem tileCount_iff_le_200_of9 (h : OpenInstances9) {N : ℕ} (h1 : 1 ≤ N) (h200 : N ≤ 200) :
    TileCount N ↔ FamC N = true :=
  tileCount_iff_le_200_of (openInstances_of9 h) h1 h200

end Erdos634.Draft.Spectrum200Cond2

#print axioms Erdos634.Draft.Spectrum200Cond2.tileCount_iff_le_200_of9
