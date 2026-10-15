/-
Draft/NSQMMain.lean — (S5').  `CN'` = `NSQMain.CN` with the S5 leaf `RAShape` (squarefree or 8·odd squarefree)
replaced by the decidable `S5pChk` (no t ≥ 2, t² ∣ N, with N/t² odd ≥ 3 or ≡ 0 mod 8), and
    not_tile_of_conditionsNSQ' (N) (h : CN' N) (D : CongruentDissection N) : False.
`cn_imp_cn'` : CN N → CN' N  (S5pChk is implied by RAShape, via RADvd).  Witnesses / controls in NSQMWitness.  No sorry, no native_decide.
-/
import Erdos634.Draft.NSQMain
import Erdos634.Draft.NSQMRA

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

/-- `CN` with the S5 leaf `RAShape N` replaced by `S5pChk N`. -/
def CN' (N : ℕ) : Prop :=
  NQChk N ∧ EllChk2 N ∧ LeafNSq N ∧ LeafHAr N ∧ LeafR N ∧ LeafE' N ∧ LeafF1p N ∧ LeafS2 N ∧ LeafS3 N ∧ LeafIso N ∧
    LeafR8 N ∧ GammaChk N ∧ S1Chk N ∧ RWChk N ∧ S5pChk N

instance (N : ℕ) : Decidable (CN' N) := by unfold CN'; infer_instance

theorem s5pChk_of_shape {N : ℕ} (hN0 : 0 < N) (h : RAShape N) : S5pChk N :=
  s5pChk_of_free (s5pFree_of_dvd hN0 (fun e f K he hef hcop hK hEq => radvd_of_shape h e f K he hef hcop hK hEq))

theorem cn_imp_cn' {N : ℕ} (h : CN N) : CN' N := by
  obtain ⟨hNQ, hEll, hNSq, hHAr, hR, hE, hF1, hS2, hS3, hIso, hG1, hG, hS1, hRW, hRA⟩ := h
  have hN0 : 0 < N := by
    obtain ⟨s, n, hs, -, hNs, h7, -⟩ := nq_of_chk hNQ
    have : 1 ≤ s ^ 2 := Nat.one_le_pow _ _ hs
    rw [hNs]; nlinarith
  exact ⟨hNQ, hEll, hNSq, hHAr, hR, hE, hF1, hS2, hS3, hIso, hG1, hG, hS1, hRW, s5pChk_of_shape hN0 hRA⟩

/-- **The non-squarefree all-N theorem with the refined S5 leaf.** -/
theorem not_tile_of_conditionsNSQ' (N : ℕ) (h : CN' N) (D : CongruentDissection N) : False := by
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
    (rwStatement_nsq N (rwFree_of_chk hRW)) (raStatement_nsqM N (s5pFree_of_chk hRA))
    (fun hS => Erdos634.Draft.NSQCaseA.gapA_of_ell_nsq hS hNQ' hns (harith_of_chk hHAr) hℓ hℓ7 hodd)
    (caseB_of_sumsq N (fun D μ τ hs => Row2.theoremS_perm_nsq D μ τ hs hNQ') hns)
    ?_ (caseG_of_gammaArith N (gammaArith_of_chk hG)) ?_ ?_ ?_ (gapR8_of_chk hF2c hF3c hF4c) D
  · rcases hR with hodd2 | ⟨hev, hnh⟩
    · exact caseR_of_odd N hodd2
    · exact caseR_of_H1 N (Erdos634.Draft.H1k.h1Right N) (nhsq_of_chk hev hnh)
  · rcases hE with h4 | ⟨h11, h60, -⟩
    · exact gapE60_of_mod4_two N h4
    · exact gapE60_of_chk' h11 h60
  · rcases hE with h4 | ⟨-, -, h120⟩
    · exact gapE120_of_mod4_two N h4
    · exact gapE120_of_chk hN0 h120
  · rcases hF1 with h4 | hf
    · exact gapF1_of_mod4_two N h4
    · exact gapF1_of_chkpar (by omega) hf

end Erdos634.Draft.NSQM

#print axioms Erdos634.Draft.NSQM.cn_imp_cn'
#print axioms Erdos634.Draft.NSQM.not_tile_of_conditionsNSQ'
