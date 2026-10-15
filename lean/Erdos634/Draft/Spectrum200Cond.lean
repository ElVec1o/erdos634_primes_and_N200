/-
Draft/Spectrum200Cond.lean -- the tile-count spectrum up to 200, conditional on ten named instances.

`Spectrum200g.tileCount_iff_le_200g` decides every `N ≤ 200` outside `132, 135, 143, 154, 156, 161, 184`.  Each of
these seven values is reduced to named instances (`Draft/OpenReductions*.lean`, `Draft/N135Red.lean`).  Hence:

    theorem tileCount_iff_le_200_of (h : OpenInstances) {N : ℕ} (h1 : 1 ≤ N) (h200 : N ≤ 200) :
        TileCount N ↔ FamC N = true

where `OpenInstances` says that the ten instances have no tiling (for `135` and for the `γ = 2α` leaf of `156` in
the form of a pair statement about tilings with that number of tiles).

`OpenInstances` is false: its field `i143 : F2Inst143` is refuted by the kernel-checked
143-tiling (`Draft.N143.not_f2Inst143`, `Draft.N143.openInstances_false`), so `tileCount_iff_le_200_of` and
`not_tileCount_of` are vacuous.  The statement to use is `Draft.N143.tileCount_iff_le_200_of8`
(`143` is a tile count; eight instances are left).  The file is kept because `Draft.N143` uses its reductions.

No sorry, no native_decide.
-/
import Erdos634.Draft.Spectrum200g
import Erdos634.Draft.OpenReductions143
import Erdos634.Draft.OpenReductionsNsq
import Erdos634.Draft.N135Red

namespace Erdos634.Draft.Spectrum200Cond

open Erdos634.Draft.TileCountFamilies Erdos634.Geometry Erdos634.Draft.FDDSpectrumTable Erdos634.Draft.Spectrum200d
open Erdos634.Draft.Spectrum200g Erdos634.Draft.OpenRed Erdos634.Draft.IsoInst Erdos634.Draft.GapE120Exc
open Erdos634.Draft.CompositeFinal4 Erdos634.Draft.NSQM Erdos634.Draft.NSQRW Erdos634.Draft.GPairCert

/-- **The ten instances on which the spectrum up to 200 depends** (tile, then target):
`132`: `(5,3,7)` on `(42,42,66)`; `135`: the pair `(15,27)` and its mirror, `(3,5,7)` on the equilateral triangle of
side `45`; `143`: `(3,5,7)` on `(39,55,49)`; `154`: `(8,7,13)` on `(91,91,154)`; `156`: `(12,7,16)` on
`(128,128,234)`, `(40,39,64)` on `(624,624,390)`, and the pair `(6,26)`, `(25,39,40)` on `(390,390,624)`; `161`:
`(12,7,16)` on `(112,112,161)`; `184`: `(7,8,13)` on `(104,104,184)` and `(10,21,25)` on `(184,210,250)`. -/
structure OpenInstances : Prop where
  i132 : IsoInst 5 3 7 6
  i135 : E120Pair 135 15 27
  i135' : E120Pair 135 27 15
  i143 : F2Inst143
  i154 : IsoInst 8 7 13 7
  i156 : S1Inst 2 3 4
  i156' : S5Inst 2 5 8
  i156'' : GPair 156 6 26
  i161 : S3Inst 1 3 4
  i184 : IsoInst 7 8 13 8
  i184' : S4Inst 2 2 5

/-- **The spectrum up to 200, given the ten instances.** -/
theorem tileCount_iff_le_200_of (h : OpenInstances) {N : ℕ} (h1 : 1 ≤ N) (h200 : N ≤ 200) :
    TileCount N ↔ FamC N = true := by
  by_cases hu : N ∈ undecided200g
  · simp only [undecided200g, List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨fun ⟨D⟩ => (not_tile_132_of h.i132 D).elim, fun hf => absurd hf (by decide +kernel)⟩
    · exact ⟨fun ⟨D⟩ => (Erdos634.Draft.N135.not_tile_135_of h.i135 h.i135' D).elim,
        fun hf => absurd hf (by decide +kernel)⟩
    · exact ⟨fun ⟨D⟩ => (not_tile_143_of h.i143 D).elim, fun hf => absurd hf (by decide +kernel)⟩
    · exact ⟨fun ⟨D⟩ => (not_tile_154_of h.i154 D).elim, fun hf => absurd hf (by decide +kernel)⟩
    · exact ⟨fun ⟨D⟩ => (not_tile_156_of h.i156 h.i156' h.i156'' D).elim,
        fun hf => absurd hf (by decide +kernel)⟩
    · exact ⟨fun ⟨D⟩ => (not_tile_161_of h.i161 D).elim, fun hf => absurd hf (by decide +kernel)⟩
    · exact ⟨fun ⟨D⟩ => (not_tile_184_of h.i184 h.i184' D).elim, fun hf => absurd hf (by decide +kernel)⟩
  · exact tileCount_iff_le_200g h1 h200 hu

/-- in particular, given the ten instances, none of the seven values is a tile count -/
theorem not_tileCount_of (h : OpenInstances) :
    ¬ TileCount 132 ∧ ¬ TileCount 135 ∧ ¬ TileCount 143 ∧ ¬ TileCount 154 ∧ ¬ TileCount 156 ∧ ¬ TileCount 161 ∧
      ¬ TileCount 184 :=
  ⟨fun ⟨D⟩ => not_tile_132_of h.i132 D, fun ⟨D⟩ => Erdos634.Draft.N135.not_tile_135_of h.i135 h.i135' D,
   fun ⟨D⟩ => not_tile_143_of h.i143 D, fun ⟨D⟩ => not_tile_154_of h.i154 D,
   fun ⟨D⟩ => not_tile_156_of h.i156 h.i156' h.i156'' D, fun ⟨D⟩ => not_tile_161_of h.i161 D,
   fun ⟨D⟩ => not_tile_184_of h.i184 h.i184' D⟩

end Erdos634.Draft.Spectrum200Cond

#print axioms Erdos634.Draft.Spectrum200Cond.tileCount_iff_le_200_of
