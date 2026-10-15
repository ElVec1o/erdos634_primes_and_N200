/-
Draft/Spectrum200Cond4.lean -- `154` and `156` are not tile counts; the spectrum up to 200 on four values.

Kernel-checked certificates (exact replays of search trees found with the isosceles target standing on a leg):
* `Refl.MS1N156.not_dissection` (234,239 nodes) gives `S1Inst 2 3 4`, hence `N156.not_tile_156`;
* `Refl.MISO154.not_dissection` (63,895 nodes) gives `IsoInst 8 7 13 7`, hence `N154F.not_tile_154`;
* `Refl.MS4N184.not_dissection` (71,173 nodes) gives `S4Inst 2 2 5` (`s4inst_2_2_5` below), one of the two instances
  of `184`.

`OpenInstances5` states that the following four instances have no tiling: `132`: `(5,3,7)` on `(42,42,66)`; `135`: the pair `(15,27)` and its
mirror; `161`: `(12,7,16)` on `(112,112,161)`; `184`: `(7,8,13)` on `(104,104,184)`.

    theorem tileCount_iff_le_200_of5 (h : OpenInstances5) {N : ℕ} (h1 : 1 ≤ N) (h200 : N ≤ 200) :
        TileCount N ↔ FamD N = true

That `154` is not a tile count was announced earlier by D. Paliy (computer-assisted, unrefereed); the theorem here is a
kernel-checked confirmation.

No sorry, no native_decide.
-/
import Erdos634.Draft.N143
import Erdos634.Draft.N156Final
import Erdos634.Draft.N154Final
import Erdos634.Draft.InstLbl
import Erdos634.Refl.MS4N184Sound

open scoped Classical
set_option maxRecDepth 8000
set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000

namespace Erdos634.Draft.Spectrum200Cond4

open Erdos634.Geometry Erdos634.CertNode Erdos634.CertCoord Erdos634.Draft.OpenRed
open Erdos634.Draft.TileCountFamilies Erdos634.Draft.InstLbl Erdos634.Draft.IsoInst Erdos634.Draft.NSQRW
open Erdos634.Draft.Spectrum200d Erdos634.Draft.Spectrum200g Erdos634.Draft.GapE120Exc
open Erdos634.Draft.CompositeFinal4 Erdos634.Draft.NSQM Erdos634.Draft.GPairCert Erdos634.Draft.N143

theorem TGT_S4N184 : dist (Refl.MS4N184.TGT.pts 0) (Refl.MS4N184.TGT.pts 1) = 184 ∧
    dist (Refl.MS4N184.TGT.pts 1) (Refl.MS4N184.TGT.pts 2) = 210 ∧
    dist (Refl.MS4N184.TGT.pts 0) (Refl.MS4N184.TGT.pts 2) = 250 :=
  model_sides_rp Refl.MS4N184.hDn Refl.MS4N184.TGT_pos (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

/-- S4 `(S', e, f) = (2, 2, 5)`: tile `(10, 21, 25)`, target `(184, 210, 250)`. -/
theorem s4inst_2_2_5 : S4Inst 2 2 5 :=
  s4inst_of_cert_lbl 2 2 5 Refl.MS4N184.TGT Refl.MS4N184.MODEL
    ⟨by rw [TGT_S4N184.1]; norm_num, by rw [TGT_S4N184.2.1]; norm_num, by rw [TGT_S4N184.2.2]; norm_num⟩
    ⟨by rw [Refl.MS4N184.MODEL_sides.1]; norm_num, by rw [Refl.MS4N184.MODEL_sides.2.1]; norm_num,
      by rw [Refl.MS4N184.MODEL_sides.2.2]; norm_num⟩
    (fun D hT hM => Refl.MS4N184.not_dissection D hT hM)

/-- **`154` and `156` are not tile counts.** -/
theorem decided_154_156 : ¬ TileCount 154 ∧ ¬ TileCount 156 :=
  ⟨Erdos634.Draft.N154F.not_tileCount_154, Erdos634.Draft.N156.not_tileCount_156⟩

/-- **`184` from its last instance.** -/
theorem not_tile_184_of_iso (h : IsoInst 7 8 13 8) (D : CongruentDissection 184) : False :=
  not_tile_184_of h (@s4inst_2_2_5) D

/-- **The five instances on which the spectrum up to 200 depends** (tile, then target): `132`: `(5,3,7)` on
`(42,42,66)`; `135`: the pair `(15,27)` and its mirror, `(3,5,7)` on the equilateral triangle of side `45`; `161`:
`(12,7,16)` on `(112,112,161)`; `184`: `(7,8,13)` on `(104,104,184)`. -/
structure OpenInstances5 : Prop where
  i132 : IsoInst 5 3 7 6
  i135 : E120Pair 135 15 27
  i135' : E120Pair 135 27 15
  i161 : S3Inst 1 3 4
  i184 : IsoInst 7 8 13 8

/-- **The spectrum up to 200, given the five open instances**: four values (`132, 135, 161, 184`) depend on them. -/
theorem tileCount_iff_le_200_of5 (h : OpenInstances5) {N : ℕ} (h1 : 1 ≤ N) (h200 : N ≤ 200) :
    TileCount N ↔ FamD N = true := by
  by_cases h143 : N = 143
  · subst h143
    exact ⟨fun _ => by decide +kernel, fun _ => tileCount_143⟩
  have hD : FamD N = FamC N := by
    have : (N == 143) = false := by simpa using h143
    simp [FamD, this]
  rw [hD]
  by_cases hu : N ∈ undecided200g
  · simp only [undecided200g, List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨fun ⟨D⟩ => (not_tile_132_of h.i132 D).elim, fun hf => absurd hf (by decide +kernel)⟩
    · exact ⟨fun ⟨D⟩ => (Erdos634.Draft.N135.not_tile_135_of h.i135 h.i135' D).elim,
        fun hf => absurd hf (by decide +kernel)⟩
    · exact absurd rfl h143
    · exact ⟨fun ⟨D⟩ => (Erdos634.Draft.N154F.not_tile_154 D).elim, fun hf => absurd hf (by decide +kernel)⟩
    · exact ⟨fun ⟨D⟩ => (Erdos634.Draft.N156.not_tile_156 D).elim, fun hf => absurd hf (by decide +kernel)⟩
    · exact ⟨fun ⟨D⟩ => (not_tile_161_of h.i161 D).elim, fun hf => absurd hf (by decide +kernel)⟩
    · exact ⟨fun ⟨D⟩ => (not_tile_184_of_iso h.i184 D).elim, fun hf => absurd hf (by decide +kernel)⟩
  · exact tileCount_iff_le_200g h1 h200 hu

end Erdos634.Draft.Spectrum200Cond4

#print axioms Erdos634.Draft.Spectrum200Cond4.decided_154_156
#print axioms Erdos634.Draft.Spectrum200Cond4.s4inst_2_2_5
#print axioms Erdos634.Draft.Spectrum200Cond4.tileCount_iff_le_200_of5
