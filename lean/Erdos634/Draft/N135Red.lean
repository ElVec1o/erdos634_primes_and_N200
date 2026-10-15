/-
Draft/N135Red.lean -- `N = 135` reduced to one instance.

`135 = 15 · 3²`.  Every leaf of the non-squarefree chain is closed in Lean except one pair of the `2π/3` tile on the
equilateral triangle:

    theorem not_tile_135_of (h1 : E120Pair 135 15 27) (h2 : E120Pair 135 27 15) (D : CongruentDissection 135) : False

The pairs `(s, t)` of `Row5.theoremE_twoPiThree` at `N = 135` are the factorizations of `405` with `s, t ≤ 135`:
`(3, 135)`, `(5, 81)`, `(9, 45)`, `(15, 27)` and their mirrors.  The first three have the non-square discriminants
`19584`, `7936`, `3456` and are excluded by `E120Irr.e120Pair_of_not_isSquare`.  The pair `(15, 27)` has the
discriminant `2304 = 48²`: it is the tile `(3, 5, 7)` on the equilateral triangle of side `45`.

So `135` is a tile count if and only if `(3, 5, 7)` tiles the equilateral triangle of side `45` with `135` tiles.
This file does not decide `135`.

No sorry, no native_decide.
-/
import Erdos634.Draft.ChainGapA
import Erdos634.Draft.GAUFinal
import Erdos634.Draft.E60Apps
import Erdos634.Draft.GPairs132
import Erdos634.Draft.E120Irr
import Erdos634.Draft.RAInst
import Erdos634.Draft.AtomShape
import Erdos634.Refl.MS135Sound
import Erdos634.Draft.TileCountFamilies

open scoped Classical
set_option maxRecDepth 8000
set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000

namespace Erdos634.Draft.N135

open Erdos634.Geometry Erdos634.Draft.TheoremPConditional Erdos634.Draft.Chain15 Erdos634.Draft.ChainComposite
open Erdos634.Draft.CompositeGen2 Erdos634.Draft.CompositeArith Erdos634.Draft.CompositeS2Arith
open Erdos634.Draft.CompositeS1Arith Erdos634.Draft.CompositeIsoB Erdos634.Draft.CompositeFinal2
open Erdos634.Draft.CompositeFinal3 Erdos634.Draft.AllNExclusion Erdos634.Draft.AllN2
open Erdos634.Draft.NSQRA Erdos634.Draft.NSQRW Erdos634.Draft.NSQS1 Erdos634.Draft.NSQChk Erdos634.Draft.NSQLegs
open Erdos634.Draft.NSQMain Erdos634.Draft.NSQM Erdos634.CertNode Erdos634.CertCoord
open Erdos634.Draft.N566076 Erdos634.Draft.IsoInst Erdos634.Draft.ChainIso Erdos634.Draft.R8ZF
open Erdos634.Draft.GapE120Exc Erdos634.Draft.E120Irr

theorem s1_135 : S1Closed 135 := s1Closed_of_free 135 (s1Free_of_chk (by decide +kernel))

theorem s3_135 : S3Closed 135 := s3Closed_of_isoQRef 135 (isoQRef_of_chk (by norm_num) (by decide +kernel))

theorem iso_135 : IsoClosed 135 := isoClosed_of_chk (by norm_num) (by decide +kernel)

theorem s4_135 : RWStatementNsq 135 := rwStatement_nsq 135 (rwFree_of_chk (by decide +kernel))

/-! ## S5: the instances `(3, 1, 4)` (dead by `t e < f`) and `(3, 7, 8)` (certificate `Refl.MS135`) -/

theorem TGT_S : dist (Refl.MS135.TGT.pts 0) (Refl.MS135.TGT.pts 1) = 315 ∧
    dist (Refl.MS135.TGT.pts 1) (Refl.MS135.TGT.pts 2) = 360 ∧ dist (Refl.MS135.TGT.pts 0) (Refl.MS135.TGT.pts 2) = 360 :=
  model_sides_rp Refl.MS135.hDn Refl.MS135.TGT_pos (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

/-- S5 `(t,e,f) = (3,7,8)`: tile `(56,15,64)`, target `(360,360,315)`. -/
theorem s5inst_3_7_8 : S5Inst 3 7 8 :=
  s5inst_of_cert 3 7 8 Refl.MS135.TGT Refl.MS135.MODEL
    ⟨by rw [TGT_S.1]; norm_num, by rw [TGT_S.2.1]; norm_num, by rw [TGT_S.2.2]; norm_num⟩
    ⟨by rw [Refl.MS135.MODEL_sides.1]; norm_num, by rw [Refl.MS135.MODEL_sides.2.1]; norm_num,
      by rw [Refl.MS135.MODEL_sides.2.2]; norm_num⟩
    (fun D hT hM => Refl.MS135.not_dissection D hT hM)

/-- S5 `(t,e,f) = (3,1,4)`: `t e < f` -/
theorem s5inst_3_1_4 : S5Inst 3 1 4 :=
  s5inst_of_te_lt (by norm_num) (by norm_num) (by norm_num) isCoprime_one_left (by norm_num)

theorem s5_135 : RAStatementNsq 135 := by
  refine raStatement_of_inst 135 ?_
  intro t e f ht he hef hcop hN
  push_cast at hN
  have hd : 2 * f - 1 ≤ f ^ 2 - e ^ 2 := by nlinarith
  have ht4 : 4 ≤ t ^ 2 := by nlinarith
  have hf : f ≤ 17 := by nlinarith
  have hf2 : 2 ≤ f := by omega
  have ht5 : t ≤ 6 := by
    by_contra h; push_neg at h
    have : 49 ≤ t ^ 2 := by nlinarith
    nlinarith
  interval_cases t <;> interval_cases f <;> interval_cases e <;>
    first | (norm_num at hN; done) | exact @s5inst_3_7_8 | exact @s5inst_3_1_4

theorem f1_135 : GapF1 135 := gapF1_of_chk (by norm_num) (by decide +kernel)

theorem r8_135 : GapR8 135 := gapR8_of_chk_z (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- the pair table of `135`: only `(15, 27)` and its mirror have a square discriminant -/
theorem pairs120_135 : Pairs120ChkSq 135 [(15, 27), (27, 15)] := by decide +kernel

/-- the table is sharp: without the two listed pairs it fails -/
theorem pairs120_135_sharp : ¬ Pairs120ChkSq 135 [] := by decide +kernel

/-- **`GapE120 135` from the pair `(15, 27)` and its mirror.** -/
theorem gapE120_135_of (h1 : E120Pair 135 15 27) (h2 : E120Pair 135 27 15) : GapE120 135 := by
  refine gapE120_of_chk_sq [(15, 27), (27, 15)] pairs120_135 ?_
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h1
  · exact h2

/-- **`135` is not a tile count, given the one remaining pair.** -/
theorem not_tile_135_of (h1 : E120Pair 135 15 27) (h2 : E120Pair 135 27 15)
    (D : CongruentDissection 135) : False :=
  Erdos634.Draft.ChainGapA.not_tile_nsq_gapA 135 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) s1_135 s3_135 iso_135 s4_135 s5_135 Erdos634.Draft.GPairs132.caseG135
    Erdos634.Draft.GAU.gapA_135 Erdos634.Draft.E60Apps.gapE60_135 (gapE120_135_of h1 h2) f1_135 r8_135 D

/-- **`135` is a tile count if and only if the one remaining pair is realized.**  The two mirror pairs describe
the same tile, `(3, 5, 7)` on the equilateral triangle of side `45`. -/
theorem tileCount_135_iff :
    Erdos634.Draft.TileCountFamilies.TileCount 135 ↔ ¬ (E120Pair 135 15 27 ∧ E120Pair 135 27 15) := by
  constructor
  · rintro ⟨D⟩ ⟨h1, h2⟩
    exact not_tile_135_of h1 h2 D
  · intro h
    by_contra hT
    apply h
    constructor
    · intro D α a b c _ _ _ _ _ _
      exact hT ⟨D⟩
    · intro D α a b c _ _ _ _ _ _
      exact hT ⟨D⟩

end Erdos634.Draft.N135

#print axioms Erdos634.Draft.N135.not_tile_135_of
#print axioms Erdos634.Draft.N135.tileCount_135_iff
