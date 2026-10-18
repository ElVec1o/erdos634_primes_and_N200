/-
Draft/NSQMMainZETW.lean — `CN'zETW` = `CN'zET` (`NSQMMainZET`) with the S5 leaf `S5pChk` replaced by the S5 word leaf `S5wChk`
(`NSQMS5W`: no S5 instance `N = t^2 (f^2-e^2)` has a base word `x ef + y (f^2-e^2) + z f^2 = t e (f^2-e^2)`, `z >= f`;
`SideRunGThetaMain.theta_word_hasSides` via `ThetaKill.theta_word`).  The S5 conclusion is `NSQMS5W.raStatement_of_s5w`.
Sound for every N.  Census leaf: `leaf_s5w` in `rust/allncond2/src/nsq.rs` (`--nsq-etw`).
    No sorry, no native_decide.
-/
import Erdos634.Draft.NSQMain
import Erdos634.Draft.NSQMRA
import Erdos634.Draft.R8ZFLeaf
import Erdos634.Draft.NSQMMainZ
import Erdos634.Draft.E60Irr
import Erdos634.Draft.NSQRWT
import Erdos634.Draft.NSQMS5W
import Erdos634.Draft.NSQMMainZET

set_option maxRecDepth 8000
set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000

namespace Erdos634.Draft.NSQM

open Erdos634.Geometry Erdos634.Draft.TheoremPConditional Erdos634.Draft.Chain15 Erdos634.Draft.ChainComposite
open Erdos634.Draft.CompositeGen2 Erdos634.Draft.CompositeArith Erdos634.Draft.CompositeS2Arith
open Erdos634.Draft.CompositeS1Arith Erdos634.Draft.CompositeIsoB Erdos634.Draft.CompositeFinal2
open Erdos634.Draft.CompositeFinal3 Erdos634.Draft.AllNExclusion Erdos634.Draft.AllN2
open Erdos634.Draft.NSQRA Erdos634.Draft.NSQRW Erdos634.Draft.NSQS1 Erdos634.Draft.NSQChk Erdos634.Draft.NSQLegs
open Erdos634.Draft.NSQMain

open Erdos634.Draft.R8ZF Erdos634.Draft.E60Irr
open Erdos634.Draft.NSQRWT

def CN'zETW (N : ℕ) : Prop :=
  NQChk N ∧ EllChk2 N ∧ LeafNSq N ∧ LeafHAr N ∧ LeafR N ∧ LeafEsqN N ∧ LeafF1p N ∧ LeafS2 N ∧ LeafS3 N ∧ LeafIso N ∧
    LeafR8z N ∧ GammaChk N ∧ S1Chk N ∧ RWChkT N ∧ S5wChk N

instance (N : ℕ) : Decidable (CN'zETW N) := by unfold CN'zETW; infer_instance

/-- **The non-squarefree all-N theorem with the S5 word leaf (`S5wChk`, `NSQMS5W`).** -/
theorem not_tile_of_conditionsNSQzETW (N : ℕ) (h : CN'zETW N) (D : CongruentDissection N) : False := by
  obtain ⟨hNQ, hEll, hNSq, hHAr, hR, hE, hF1, hS2, hS3, hIso, ⟨hF2c, hF3c, hF4c⟩, hG, hS1, hRW, hRA⟩ := h
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
    (rwStatement_nsqT N (rwFreeT_of_chk hRW)) (raStatement_of_s5w N hRA)
    (fun hS => Erdos634.Draft.NSQCaseA.gapA_of_ell_nsq hS hNQ' hns (harith_of_chk hHAr) hℓ hℓ7 hodd)
    (caseB_of_sumsq N (fun D μ τ hs => Row2.theoremS_perm_nsq D μ τ hs hNQ') hns)
    ?_ (caseG_of_gammaArith N (gammaArith_of_chk hG)) ?_ ?_ ?_ (gapR8_of_chk_z hF2c hF3c hF4c) D
  · rcases hR with hodd2 | ⟨hev, hnh⟩
    · exact caseR_of_odd N hodd2
    · exact caseR_of_H1 N (Erdos634.Draft.H1k.h1Right N) (nhsq_of_chk hev hnh)
  · rcases hE with h4 | ⟨h11, h60, -⟩
    · exact gapE60_of_mod4_two N h4
    · exact gapE60_of_chk_sq h11 [] h60 (by intro p hp; cases hp)
  · rcases hE with h4 | ⟨-, -, h120⟩
    · exact gapE120_of_mod4_two N h4
    · exact gapE120_of_chk hN0 h120
  · rcases hF1 with h4 | hf
    · exact gapF1_of_mod4_two N h4
    · exact gapF1_of_chkpar (by omega) hf

end Erdos634.Draft.NSQM

#print axioms Erdos634.Draft.NSQM.not_tile_of_conditionsNSQzETW
