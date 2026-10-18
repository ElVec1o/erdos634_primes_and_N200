/-
Draft/ThmDChainWS.lean -- `CN'zETWDS` = `CN'zETWD` with the S1 leaf replaced by `S1Chk N ∨ S1tChk N` (the sharpened S1 leaf of
`NSQS1T`: `t >= 2` instances with `2 t p < q` are killed by `cor:ebelow(b)`).  `S1Chk N -> S1tChk N`, so the disjunction is `S1tChk N`.
`not_tile_of_conditionsNSQzETWDS : CN'zETWDS N -> CongruentDissection N -> False`.  The older theorems are kept.
Witnesses: `cnzETWDS_428` (428 = 4 * 107, S1 plain fails, S1t holds), `not_cnzETWD_428`, `cnzETWDS_not_72`.
No sorry, no native_decide.
-/
import Erdos634.Draft.ThmDChainW
import Erdos634.Draft.NSQS1T

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
open Erdos634.Draft.NSQS1T (S1tChk)

def CN'zETWDS (N : ℕ) : Prop :=
  NQChk N ∧ EllChk2 N ∧ LeafNSq N ∧ LeafHAr N ∧ LeafR N ∧ LeafEsqN N ∧ LeafF1p N ∧ LeafS2 N ∧ LeafS3 N ∧ LeafIso N ∧
    LeafR8z N ∧ Erdos634.Draft.ThmD.GammaChkD N ∧ (S1Chk N ∨ S1tChk N) ∧ RWChkT N ∧ S5wChk N

instance (N : ℕ) : Decidable (CN'zETWDS N) := by unfold CN'zETWDS; infer_instance

/-- **The non-squarefree all-N theorem with D', the S5 word leaf and the sharpened S1 leaf.** -/
theorem not_tile_of_conditionsNSQzETWDS (N : ℕ) (h : CN'zETWDS N) (D : CongruentDissection N) : False := by
  obtain ⟨hNQ, hEll, hNSq, hHAr, hR, hE, hF1, hS2, hS3, hIso, ⟨hF2c, hF3c, hF4c⟩, hG, hS1, hRW, hRA⟩ := h
  have hS1c : S1Closed N := by
    rcases hS1 with h1 | h1
    · exact s1Closed_of_free N (s1Free_of_chk h1)
    · exact Erdos634.Draft.NSQS1T.s1tClosed_of_free N (Erdos634.Draft.NSQS1T.s1tFree_of_chk h1)
  have hNQ' : Erdos634.Geometry.NQ N := nq_of_chk hNQ
  have hN7 : 7 ≤ N := by
    obtain ⟨s, n, hs, -, hNs, h7, -⟩ := hNQ'
    have : 1 ≤ s ^ 2 := Nat.one_le_pow _ _ hs
    rw [hNs]; nlinarith
  have hN0 : 0 < N := by omega
  have hns : ¬ ∃ x y : ℕ, N = x ^ 2 + y ^ 2 := nsq_of_chk hNSq
  obtain ⟨ℓ, hℓ, hℓ7, hodd⟩ := ell_of_chk2 hEll
  refine chain_nsq N (hS1c)
    (s2Closed_of_arith N (s2Arith_of_chk hN0 hS2))
    (s3Closed_of_isoQRef N (isoQRef_of_chk hN0 hS3))
    (isoH9b_of_chk hN0 hIso)
    (rwStatement_nsqT N (rwFreeT_of_chk hRW)) (raStatement_of_s5w N hRA)
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


theorem cnzETWDS_of_cnzETWD {N : ℕ} (h : CN'zETWD N) : CN'zETWDS N := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15⟩ := h
  exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, Or.inl a13, a14, a15⟩

theorem cnzETWDS_428 : CN'zETWDS 428 := by decide +kernel
theorem not_s1Chk_428 : ¬ S1Chk 428 := by decide +kernel
theorem not_cnzETWD_428 : ¬ CN'zETWD 428 := by decide +kernel
theorem cnzETWDS_not_72 : ¬ CN'zETWDS 72 := by decide +kernel

/-- 428 tiles is excluded by the new chain (and not by the old). -/
theorem no_dissection_428 (D : CongruentDissection 428) : False := not_tile_of_conditionsNSQzETWDS 428 cnzETWDS_428 D

end Erdos634.Draft.NSQM

#print axioms Erdos634.Draft.NSQM.not_tile_of_conditionsNSQzETWDS
#print axioms Erdos634.Draft.NSQM.cnzETWDS_428
#print axioms Erdos634.Draft.NSQM.not_cnzETWD_428
#print axioms Erdos634.Draft.NSQM.cnzETWDS_not_72
#print axioms Erdos634.Draft.NSQM.no_dissection_428
