/-
Draft/N60AChain.lean -- N = 60: `chain_nsq` instantiated at 60 with B, F1, S4 (RW), R8, S1, S2, S3, Iso, R, NSq discharged
by decidable checks (decide +kernel) and existing N-general lemmas.  Exactly FIVE residual hypotheses remain:
    GapA 60, CaseGClosed 60, GapE60 60, GapE120 60, RAStatementNsq 60
(S5: the two instances (K,M) = (30,2) -> (e,f) = (7,8) and (10,6) -> (1,4), t = 2; RADvd 60 / S5pChk 60 are FALSE.)
R8 uses `R8ZFLeaf.gapR8_of_chk_z` (NoF3z, not NoF3: NoF3 60 is false but NoF3z 60 holds).
  CONDITIONAL on five leaves; NOT an exclusion of 60. ***
-/
import Erdos634.Draft.NSQMain
import Erdos634.Draft.NSQMMain
import Erdos634.Draft.R8ZFLeaf

set_option maxRecDepth 8000
set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000

namespace Erdos634.Draft.N60A

open Erdos634.Geometry Erdos634.Draft.TheoremPConditional Erdos634.Draft.Chain15 Erdos634.Draft.ChainComposite
open Erdos634.Draft.CompositeGen2 Erdos634.Draft.CompositeArith Erdos634.Draft.CompositeS2Arith
open Erdos634.Draft.CompositeS1Arith Erdos634.Draft.CompositeIsoB Erdos634.Draft.CompositeFinal2
open Erdos634.Draft.CompositeFinal3 Erdos634.Draft.AllNExclusion Erdos634.Draft.AllN2
open Erdos634.Draft.NSQRA Erdos634.Draft.NSQRW Erdos634.Draft.NSQS1 Erdos634.Draft.NSQChk Erdos634.Draft.NSQLegs
open Erdos634.Draft.NSQMain

theorem nqChk_60 : NQChk 60 := by decide +kernel
theorem nsqChk_60 : LeafNSq 60 := by decide +kernel
theorem leafR_60 : LeafR 60 := by decide +kernel
theorem leafS2_60 : LeafS2 60 := by decide +kernel
theorem leafS3_60 : LeafS3 60 := by decide +kernel
theorem leafIso_60 : LeafIso 60 := by decide +kernel
theorem s1Chk_60 : S1Chk 60 := by decide +kernel
theorem rwChk_60 : RWChk 60 := by decide +kernel
theorem f1ChkPar_60 : F1ChkPar 60 := by decide +kernel
theorem noF2Chk_60 : NoF2Chk 60 := by decide +kernel
theorem noF3zChk_60 : Erdos634.Draft.R8ZF.NoF3zChk 60 := by decide +kernel
theorem noF4zChk_60 : NoF4zChk 60 := by decide +kernel

theorem gapR8_60 : GapR8 60 := Erdos634.Draft.R8ZF.gapR8_of_chk_z noF2Chk_60 noF3zChk_60 noF4zChk_60

/-- **N = 60 modulo exactly five named leaves.** -/
theorem chain_60_final' (gA : GapA 60) (gG : CaseGClosed 60) (gE60 : GapE60 60) (gE120 : GapE120 60)
    (gS5 : RAStatementNsq 60) (D : CongruentDissection 60) : False := by
  have hNQ' : Erdos634.Geometry.NQ 60 := nq_of_chk nqChk_60
  have hN0 : 0 < 60 := by norm_num
  have hns : ¬ ∃ x y : ℕ, 60 = x ^ 2 + y ^ 2 := nsq_of_chk nsqChk_60
  refine chain_nsq 60 (s1Closed_of_free 60 (s1Free_of_chk s1Chk_60))
    (s2Closed_of_arith 60 (s2Arith_of_chk hN0 leafS2_60))
    (s3Closed_of_isoQRef 60 (isoQRef_of_chk hN0 leafS3_60))
    (isoH9b_of_chk hN0 leafIso_60)
    (rwStatement_nsq 60 (rwFree_of_chk rwChk_60)) gS5
    (fun _ => gA)
    (caseB_of_sumsq 60 (fun D μ τ hs => Row2.theoremS_perm_nsq D μ τ hs hNQ') hns)
    ?_ gG gE60 gE120 (gapF1_of_chkpar (by norm_num) f1ChkPar_60) gapR8_60 D
  rcases (show LeafR 60 from leafR_60) with hodd2 | ⟨hev, hnh⟩
  · exact caseR_of_odd 60 hodd2
  · exact caseR_of_H1 60 (Erdos634.Draft.H1k.h1Right 60) (nhsq_of_chk hev hnh)

end Erdos634.Draft.N60A

#print axioms Erdos634.Draft.N60A.chain_60_final'
