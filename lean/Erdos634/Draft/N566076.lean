/-
Draft/N566076.lean -- the composite counts `N = 56` and `N = 76` are NOT tile counts, and `N = 60` modulo `GapE60 60`.

`not_tile_of_leaves` is `NSQM.not_tile_of_conditionsNSQ'` with the search-type leaves (S4 = `RWStatementNsq`,
S5 = `RAStatementNsq`, `γ = 2α` = `CaseGClosed`, `GapE60`, `GapE120`) supplied as theorems instead of arithmetic checks.
The leaves that fail their arithmetic check are discharged by kernel-checked `Refl.CheckM` certificates:

| N  | leaf  | instance                                   | certificate                      |
|----|-------|--------------------------------------------|----------------------------------|
| 56 | E120  | tile (7,8,13), equilateral side 56         | `Refl.ME56.not_dissection` (4,655 nodes) |
| 56 | S4    | tile (6,5,9), target (30,56,54)            | `Refl.MC56.not_dissection` (409 nodes)   |
| 60 | E120  | tile (3,5,7), equilateral side 30          | `Refl.ME60.not_dissection` (14,763 nodes)|
| 60 | S5    | tile (56,15,64), target (240,240,210)      | `Refl.MS60.not_dissection` (1,414 nodes) |
| 60 | S5    | tile (4,15,16), target (120,120,30)        | `S51.s5_14_no_tiling` (older certificate)|
| 76 | S5    | tile (90,19,100), target (380,380,342)     | `Refl.MS76.not_dissection` (4,285 nodes) |
| 76 | γ=2α  | (arithmetic + `GLI.leafG_of_dissection`)   | `GLK.caseG_76`                           |

Composite-N results (`thm:frontier3` rows 56, 60; `thm:frontier4` row 76).  NOT prime-case work.
No sorry, no native_decide.
-/
import Erdos634.Draft.GapE120N
import Erdos634.Draft.RAInst
import Erdos634.Draft.RWInst
import Erdos634.Refl.MS60Sound
import Erdos634.Refl.MS76Sound
import Erdos634.Refl.MC56Sound
import Erdos634.Draft.S51Bridge
import Erdos634.Draft.NSQMMain
import Erdos634.Draft.NSQGammaChk
import Erdos634.Draft.GLKBridge
import Erdos634.Draft.ChainGapA60

open scoped Classical
set_option maxRecDepth 8000
set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000

namespace Erdos634.Draft.N566076

open Erdos634.Geometry Erdos634.Draft.TheoremPConditional Erdos634.Draft.Chain15 Erdos634.Draft.ChainComposite
open Erdos634.Draft.CompositeGen2 Erdos634.Draft.CompositeArith Erdos634.Draft.CompositeS2Arith
open Erdos634.Draft.CompositeS1Arith Erdos634.Draft.CompositeIsoB Erdos634.Draft.CompositeFinal2
open Erdos634.Draft.CompositeFinal3 Erdos634.Draft.AllNExclusion Erdos634.Draft.AllN2
open Erdos634.Draft.NSQRA Erdos634.Draft.NSQRW Erdos634.Draft.NSQS1 Erdos634.Draft.NSQChk Erdos634.Draft.NSQLegs
open Erdos634.Draft.NSQMain Erdos634.Draft.NSQM Erdos634.CertNode Erdos634.CertCoord

/-- `not_tile_of_conditionsNSQ'` with the search-type leaves supplied as theorems. -/
theorem not_tile_of_leaves (N : ℕ) (hNQ : NQChk N) (hEll : EllChk2 N) (hNSq : LeafNSq N) (hHAr : LeafHAr N)
    (hR : LeafR N) (gE60 : GapE60 N) (hF1 : LeafF1p N) (hS2 : LeafS2 N) (hS3 : LeafS3 N) (hIso : LeafIso N)
    (hR8 : LeafR8 N) (hS1 : S1Chk N)
    (gS4 : RWStatementNsq N) (gS5 : RAStatementNsq N) (gG : CaseGClosed N) (gE120 : GapE120 N)
    (D : CongruentDissection N) : False := by
  obtain ⟨hF2c, hF3c, hF4c⟩ := hR8
  have hNQ' : Erdos634.Geometry.NQ N := nq_of_chk hNQ
  have hN7 : 7 ≤ N := by
    obtain ⟨s, n, hs, -, hNs, h7, -⟩ := hNQ'
    have : 1 ≤ s ^ 2 := Nat.one_le_pow _ _ hs
    rw [hNs]; nlinarith
  have hN0 : 0 < N := by omega
  have hns : ¬ ∃ x y : ℕ, N = x ^ 2 + y ^ 2 := nsq_of_chk hNSq
  obtain ⟨ℓ, hℓ, hℓ7, hodd⟩ := ell_of_chk2 hEll
  refine chain_nsq N (s1Closed_of_free N (s1Free_of_chk hS1))
    (s2Closed_of_arith N (s2Arith_of_chk hN0 hS2))
    (s3Closed_of_isoQRef N (isoQRef_of_chk hN0 hS3))
    (isoH9b_of_chk hN0 hIso)
    gS4 gS5
    (fun hS => Erdos634.Draft.NSQCaseA.gapA_of_ell_nsq hS hNQ' hns (harith_of_chk hHAr) hℓ hℓ7 hodd)
    (caseB_of_sumsq N (fun D μ τ hs => Row2.theoremS_perm_nsq D μ τ hs hNQ') hns)
    ?_ gG gE60 gE120 ?_ (gapR8_of_chk hF2c hF3c hF4c) D
  · rcases hR with hodd2 | ⟨hev, hnh⟩
    · exact caseR_of_odd N hodd2
    · exact caseR_of_H1 N (Erdos634.Draft.H1k.h1Right N) (nhsq_of_chk hev hnh)
  · rcases hF1 with h4 | hf
    · exact gapF1_of_mod4_two N h4
    · exact gapF1_of_chkpar (by omega) hf


/-! ## the certificate instances -/

theorem TGT_S60 : dist (Refl.MS60.TGT.pts 0) (Refl.MS60.TGT.pts 1) = 210 ∧
    dist (Refl.MS60.TGT.pts 1) (Refl.MS60.TGT.pts 2) = 240 ∧ dist (Refl.MS60.TGT.pts 0) (Refl.MS60.TGT.pts 2) = 240 :=
  model_sides_rp Refl.MS60.hDn Refl.MS60.TGT_pos (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem TGT_S76 : dist (Refl.MS76.TGT.pts 0) (Refl.MS76.TGT.pts 1) = 342 ∧
    dist (Refl.MS76.TGT.pts 1) (Refl.MS76.TGT.pts 2) = 380 ∧ dist (Refl.MS76.TGT.pts 0) (Refl.MS76.TGT.pts 2) = 380 :=
  model_sides_rp Refl.MS76.hDn Refl.MS76.TGT_pos (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem TGT_S51 : dist (S51.TGT.pts 0) (S51.TGT.pts 1) = 30 ∧
    dist (S51.TGT.pts 1) (S51.TGT.pts 2) = 120 ∧ dist (S51.TGT.pts 0) (S51.TGT.pts 2) = 120 :=
  model_sides_rp S51.hD7 S51.TGT_pos (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem TGT_C56 : dist (Refl.MC56.TGT.pts 0) (Refl.MC56.TGT.pts 1) = 30 ∧
    dist (Refl.MC56.TGT.pts 1) (Refl.MC56.TGT.pts 2) = 56 ∧ dist (Refl.MC56.TGT.pts 0) (Refl.MC56.TGT.pts 2) = 54 :=
  model_sides_rp Refl.MC56.hDn Refl.MC56.TGT_pos (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

/-- S5 `(t,e,f) = (2,7,8)`: tile `(56,15,64)`, target `(240,240,210)`. -/
theorem s5inst_2_7_8 : S5Inst 2 7 8 :=
  s5inst_of_cert 2 7 8 Refl.MS60.TGT Refl.MS60.MODEL
    ⟨by rw [TGT_S60.1]; norm_num, by rw [TGT_S60.2.1]; norm_num, by rw [TGT_S60.2.2]; norm_num⟩
    ⟨by rw [Refl.MS60.MODEL_sides.1]; norm_num, by rw [Refl.MS60.MODEL_sides.2.1]; norm_num,
      by rw [Refl.MS60.MODEL_sides.2.2]; norm_num⟩
    (fun D hT hM => Refl.MS60.not_dissection D hT hM)

/-- S5 `(t,e,f) = (2,1,4)`: tile `(4,15,16)`, target `(120,120,30)`. -/
theorem s5inst_2_1_4 : S5Inst 2 1 4 :=
  s5inst_of_cert 2 1 4 S51.TGT S51.MODEL
    ⟨by rw [TGT_S51.1]; norm_num, by rw [TGT_S51.2.1]; norm_num, by rw [TGT_S51.2.2]; norm_num⟩
    ⟨by rw [S51.MODEL_sides.1]; norm_num, by rw [S51.MODEL_sides.2.1]; norm_num,
      by rw [S51.MODEL_sides.2.2]; norm_num⟩
    (fun D hT hM => S51.s5_14_no_tiling D hT hM)

/-- S5 `(t,e,f) = (2,9,10)`: tile `(90,19,100)`, target `(380,380,342)`. -/
theorem s5inst_2_9_10 : S5Inst 2 9 10 :=
  s5inst_of_cert 2 9 10 Refl.MS76.TGT Refl.MS76.MODEL
    ⟨by rw [TGT_S76.1]; norm_num, by rw [TGT_S76.2.1]; norm_num, by rw [TGT_S76.2.2]; norm_num⟩
    ⟨by rw [Refl.MS76.MODEL_sides.1]; norm_num, by rw [Refl.MS76.MODEL_sides.2.1]; norm_num,
      by rw [Refl.MS76.MODEL_sides.2.2]; norm_num⟩
    (fun D hT hM => Refl.MS76.not_dissection D hT hM)

/-- S4 `(S',e,f) = (2,2,3)`: tile `(6,5,9)`, target `(30,56,54)`. -/
theorem s4inst_2_2_3 : S4Inst 2 2 3 :=
  s4inst_of_cert 2 2 3 Refl.MC56.TGT Refl.MC56.MODEL
    ⟨by rw [TGT_C56.1]; norm_num, by rw [TGT_C56.2.1]; norm_num, by rw [TGT_C56.2.2]; norm_num⟩
    ⟨by rw [Refl.MC56.MODEL_sides.1]; norm_num, by rw [Refl.MC56.MODEL_sides.2.1]; norm_num,
      by rw [Refl.MC56.MODEL_sides.2.2]; norm_num⟩
    (fun D hT hM => Refl.MC56.not_dissection D hT hM)

/-! ## the leaves -/

/-- **`RAStatementNsq 60`** (S5): the two scaled instances `(2,1,4)`, `(2,7,8)`. -/
theorem ra60 : RAStatementNsq 60 := by
  refine raStatement_of_inst 60 ?_
  intro t e f ht he hef hcop hN
  push_cast at hN
  have hd : 2 * f - 1 ≤ f ^ 2 - e ^ 2 := by nlinarith
  have ht4 : 4 ≤ t ^ 2 := by nlinarith
  have hf : f ≤ 8 := by nlinarith
  have ht5 : t ≤ 4 := by
    by_contra h; push_neg at h
    have : 25 ≤ t ^ 2 := by nlinarith
    nlinarith
  have hf2 : 2 ≤ f := by omega
  interval_cases t <;> interval_cases f <;> interval_cases e <;>
    first | (norm_num at hN; done) | exact @s5inst_2_7_8 | exact @s5inst_2_1_4

/-- **`RAStatementNsq 76`** (S5): the scaled instance `(2,9,10)`. -/
theorem ra76 : RAStatementNsq 76 := by
  refine raStatement_of_inst 76 ?_
  intro t e f ht he hef hcop hN
  push_cast at hN
  have hd : 2 * f - 1 ≤ f ^ 2 - e ^ 2 := by nlinarith
  have ht4 : 4 ≤ t ^ 2 := by nlinarith
  have hf : f ≤ 10 := by nlinarith
  have ht5 : t ≤ 5 := by
    by_contra h; push_neg at h
    have : 36 ≤ t ^ 2 := by nlinarith
    nlinarith
  have hf2 : 2 ≤ f := by omega
  interval_cases t <;> interval_cases f <;> interval_cases e <;>
    first | (norm_num at hN; done) | exact @s5inst_2_9_10

/-- **`RWStatementNsq 56`** (S4): the scaled instance `(2,2,3)`. -/
theorem rw56 : RWStatementNsq 56 := by
  refine rwStatement_of_inst 56 ?_
  intro S' e f hS he hef hcop hN
  push_cast at hN
  have hd : f ^ 2 + 2 * f - 1 ≤ 2 * f ^ 2 - e ^ 2 := by nlinarith
  have hS4 : 4 ≤ S' ^ 2 := by nlinarith
  have hf2 : 2 ≤ f := by omega
  have hf : f ≤ 3 := by nlinarith
  have hS5 : S' ≤ 3 := by
    by_contra h; push_neg at h
    have : 16 ≤ S' ^ 2 := by nlinarith
    nlinarith
  interval_cases S' <;> interval_cases f <;> interval_cases e <;>
    first | (norm_num at hN; done) | exact @s4inst_2_2_3

/-! ## N = 56, N = 76, N = 60 -/

/-- **`56` is not a tile count** (no `CongruentDissection 56` exists). -/
theorem not_tile_56 (D : CongruentDissection 56) : False :=
  not_tile_of_leaves 56 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (gapE60_of_chk' (by norm_num) (by decide +kernel)) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    rw56 (raStatement_nsqM 56 (s5pFree_of_chk (by decide +kernel)))
    (caseG_of_gammaArith 56 (gammaArith_of_chk Erdos634.Draft.NSQLegs.gammaChk_56))
    Erdos634.Draft.GapE120N.gapE120_56 D

/-- **`76` is not a tile count** (no `CongruentDissection 76` exists). -/
theorem not_tile_76 (D : CongruentDissection 76) : False :=
  not_tile_of_leaves 76 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (gapE60_of_chk' (by norm_num) (by decide +kernel)) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (rwStatement_nsq 76 (rwFree_of_chk (by decide +kernel))) ra76 Erdos634.GLK.caseG_76
    (gapE120_of_chk (by norm_num) (by decide +kernel)) D

/-- **`N = 60` modulo the single leaf `GapE60 60`** (the `π/3` pair `(30,6)`, tile `(9+√21, 9−√21, 12)`). -/
theorem not_tile_60_of_gapE60 (gE60 : GapE60 60) (D : CongruentDissection 60) : False :=
  Erdos634.Draft.ChainGapA60.chain_60_final_GA gE60 Erdos634.Draft.GapE120N.gapE120_60 ra60 D

end Erdos634.Draft.N566076

#print axioms Erdos634.Draft.N566076.not_tile_56
#print axioms Erdos634.Draft.N566076.not_tile_76
#print axioms Erdos634.Draft.N566076.not_tile_60_of_gapE60
