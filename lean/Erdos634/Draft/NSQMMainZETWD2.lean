/-
Draft/NSQMMainZETWD2.lean -- `CN'zETWD2` = `CN'zETWD` (`ThmDChainW`: G leaf Theorem D' `GammaChkD`, S5 word leaf `S5wChk`) with the S4 leaf `RWChkT`
replaced by `RWChkT2` (`NSQRWT2`: the S+ kill `SplusThick.wTilable_not_of_small_M`).  Existing modules untouched.
`not_tile_of_conditionsNSQzETWD2 : CN'zETWD2 N -> CongruentDissection N -> False`.  The G-leaf formal input is `ThmD.thmDStatement_geo`
(as in `ThmDChainW`; the census G leaf `leaf_g2` uses only the coprime / `(2, 2(2k+1))` pairs, a subset of `GammaChkD`).
Credit: Beeson-Rosu (framework), Paliy, the S+ analysis.  UNAUDITED.  Formalization debt, NOT /goal progress.  No sorry, no native_decide.
-/
import Erdos634.Draft.NSQMain
import Erdos634.Draft.NSQMRA
import Erdos634.Draft.R8ZFLeaf
import Erdos634.Draft.NSQMMainZ
import Erdos634.Draft.E60Irr
import Erdos634.Draft.NSQRWT
import Erdos634.Draft.NSQMS5W
import Erdos634.Draft.NSQMMainZET
import Erdos634.Draft.ThmDChain
import Erdos634.Draft.NSQMMainZETW
import Erdos634.Draft.NSQRWT2
import Erdos634.Draft.NSQMMainZETW2

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
open Erdos634.Draft.NSQRWT2

def CN'zETWD2 (N : ℕ) : Prop :=
  NQChk N ∧ EllChk2 N ∧ LeafNSq N ∧ LeafHAr N ∧ LeafR N ∧ LeafEsqN N ∧ LeafF1p N ∧ LeafS2 N ∧ LeafS3 N ∧ LeafIso N ∧
    LeafR8z N ∧ Erdos634.Draft.ThmD.GammaChkD N ∧ S1Chk N ∧ RWChkT2 N ∧ S5wChk N

instance (N : ℕ) : Decidable (CN'zETWD2 N) := by unfold CN'zETWD2; infer_instance

/-- **The final chain with the S+ kill in the S4 leaf (`RWChkT2`).** -/
theorem not_tile_of_conditionsNSQzETWD2 (N : ℕ) (h : CN'zETWD2 N) (D : CongruentDissection N) : False := by
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
    (rwStatement_nsqT2 N (rwFreeT2_of_chk hRW)) (raStatement_of_s5w N hRA)
    (fun hS => Erdos634.Draft.NSQCaseA.gapA_of_ell_nsq hS hNQ' hns (harith_of_chk hHAr) hℓ hℓ7 hodd)
    (caseB_of_sumsq N (fun D μ τ hs => Row2.theoremS_perm_nsq D μ τ hs hNQ') hns)
    ?_ (Erdos634.Draft.ThmD.caseG_of_gammaChkD Erdos634.Draft.ThmD.thmDStatement_geo hG) ?_ ?_ ?_ (gapR8_of_chk_z hF2c hF3c hF4c) D
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

/-- `CN'zETW2 N → CN'zETWD2 N`: the G leaf D' only weakens `GammaChk`. -/
theorem cnzETWD2_of_cnzETW2 {N : ℕ} (h : CN'zETW2 N) : CN'zETWD2 N := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, hG, a13, a14, a15⟩ := h
  exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11,
    fun M hM hM0 hdv h3 hp hp' => Or.inl (hG M hM hM0 hdv h3 hp hp'), a13, a14, a15⟩

end Erdos634.Draft.NSQM

#print axioms Erdos634.Draft.NSQM.not_tile_of_conditionsNSQzETWD2
#print axioms Erdos634.Draft.NSQM.cnzETWD2_of_cnzETW2
