/-
Draft/LeafFixChain.lean -- `CN'zFix N`: the windowed final chain `CN'zUB` (S1BandChain) with TWO conjuncts replaced:
  S3:  `S3ChkSq N`  ->  `LeafFix.S3newChk N`   (N = r^2 (f^2-e^2)(2f^2-e^2) excluded for every coprime e<f; `ARA.theoremA_N_form_full` + rescaling wrapper `LeafFix.s3_scaled`)
  E:   `LeafEsqW N` ->  `LeafFix.LeafEsqS N`   (`Pairs120Chk` -> `E120Irr.Pairs120ChkSq`, `E120Irr.gapE120_of_chk_sq`)
The A conjunct is UNCHANGED: `EllChk2 N ∨ AsqChk N` (`GAU.gapA_sq`) is already in `CN'zUB`; only the census tool (nsq.rs `leaf_a`) lacked it.
Every other conjunct is textually identical to `CN'zUB`.  Body of `not_tile_of_conditionsNSQzFixx` = body of `not_tile_of_conditionsNSQzETWD3x`
(S1BandChain.lean:36-69) COPIED, with two changes: `s3Closed_of_isoQRef N (isoQRef_of_chk hN0 hS3)` -> `LeafFix.s3Closed_of_fix N hN0 hS3`,
and the E120 closure `gapE120_of_chk hN0 h120` -> `LeafFix.leafEsqS_gapE120 N h120`.
STRENGTH: internal audit only (`band_theorem_free` SOUND WITH GAPS; `prop:basealphadiv` statement-match MATCH; no outside check).  UNAUDITED (this module).
Not imported by any aggregate.  No sorry, no native_decide.
-/
import Erdos634.Draft.S1BandChain
import Erdos634.Draft.LeafFixS3
import Erdos634.Draft.LeafFixE

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
open Erdos634.Draft.AllN3
open Erdos634.Draft.LeafFix

def CN'zFixx (N : ℕ) (S : Prop) : Prop :=
  NQChk N ∧ (EllChk2 N ∨ AsqChk N) ∧ LeafNSq N ∧ LeafHAr N ∧ LeafR N ∧ LeafEsqS N ∧ LeafF1p N ∧ LeafS2 N ∧ S3newChk N ∧ LeafIso N ∧
    LeafR8z N ∧ Erdos634.Draft.ThmD.GammaChkD N ∧ S ∧ RWChkT2 N ∧ S5wChk N

theorem not_tile_of_conditionsNSQzFixx (N : ℕ) (S : Prop) (hcl : S → S1Closed N) (h : CN'zFixx N S)
    (D : CongruentDissection N) : False := by
  obtain ⟨hNQ, hEll, hNSq, hHAr, hR, hE, hF1, hS2, hS3, hIso, ⟨hF2c, hF3c, hF4c⟩, hG, hS1, hRW, hRA⟩ := h
  have hNQ' : Erdos634.Geometry.NQ N := nq_of_chk hNQ
  have hN7 : 7 ≤ N := by
    obtain ⟨s, n, hs, -, hNs, h7, -⟩ := hNQ'
    have : 1 ≤ s ^ 2 := Nat.one_le_pow _ _ hs
    rw [hNs]; nlinarith
  have hN0 : 0 < N := by omega
  have hns : ¬ ∃ x y : ℕ, N = x ^ 2 + y ^ 2 := nsq_of_chk hNSq
  have hA : GapAcomp N := by
    rcases hEll with hEll | ⟨s, -, hs, hd⟩
    · obtain ⟨ℓ, hℓ, hℓ7, hodd⟩ := ell_of_chk2 hEll
      exact fun hS => Erdos634.Draft.NSQCaseA.gapA_of_ell_nsq hS hNQ' hns (harith_of_chk hHAr) hℓ hℓ7 hodd
    · intro _
      rcases hd with h | h
      · have e : N = 15 * s ^ 2 := by rw [h]; ring
        rw [e]; exact Erdos634.Draft.GAU.gapA_sq (d := 15) (s := s) (Or.inl rfl) hs
      · have e : N = 30 * s ^ 2 := by rw [h]; ring
        rw [e]; exact Erdos634.Draft.GAU.gapA_sq (d := 30) (s := s) (Or.inr rfl) hs
  refine chain_nsq N (hcl hS1)
    (s2Closed_of_arith N (s2Arith_of_chk hN0 hS2))
    (s3Closed_of_fix N hN0 hS3)
    (isoH9b_of_chk hN0 hIso)
    (rwStatement_nsqT2 N (rwFreeT2_of_chk hRW)) (raStatement_of_s5w N hRA)
    hA
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
    · exact leafEsqS_gapE120 N h120
  · rcases hF1 with h4 | hf
    · exact gapF1_of_mod4_two N h4
    · exact gapF1_of_chkpar (by omega) hf

/-- The windowed final chain with the S1 leaf extended by U2 and band (as `CN'zUB`), with the corrected S3 and E leaves. -/
def CN'zFix (N : ℕ) : Prop :=
  NQChkW N ∧ (EllChk2 N ∨ AsqChk N) ∧ NSqChkSq N ∧ HArithChkSq N ∧
    (N % 2 = 1 ∨ (N % 2 = 0 ∧ NHSqChkSq N)) ∧ LeafEsqS N ∧ (N % 4 = 2 ∨ F1ChkParW N) ∧ S2ChkSq N ∧ S3newChk N ∧ IsoH9bChkW N ∧
    (NoF2ChkSq N ∧ NoF3zChkSq N ∧ NoF4zChkSq N) ∧ GammaChkDW N ∧ Erdos634.Draft.S1Band.S1UBChkW N ∧ RWChkT2W N ∧ S5wChkW N

instance (N : ℕ) : Decidable (CN'zFix N) := by unfold CN'zFix; infer_instance

theorem cnzFixx_of_Fix {N : ℕ} (h : CN'zFix N) : CN'zFixx N (Erdos634.Draft.S1Band.S1UBChkW N) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, ⟨a, b, c⟩, h12, h13, h14, h15⟩ := h
  refine ⟨nqChk_of_W h1, h2, nsqChk_of_sq h3, hArithChk_of_sq h4, ?_, h6, ?_, s2Chk_of_sq h8, h9,
    isoH9bChk_of_W h10, ⟨noF2Chk_of_sq a, noF3zChk_of_sq b, noF4zChk_of_sq c⟩, gammaChkD_of_W h12, h13,
    rwChkT2_of_W h14, s5wChk_of_W h15⟩
  · rcases h5 with h | ⟨h, h'⟩
    · exact Or.inl h
    · exact Or.inr ⟨h, nhsqChk_of_sq h'⟩
  · rcases h7 with h | h
    · exact Or.inl h
    · exact Or.inr (f1ChkPar_of_W h)

/-- **The final chain with the corrected S3 and E leaves.**  Conclusion identical to `not_tile_of_conditionsNSQzUB`. -/
theorem not_tile_of_conditionsNSQzFix (N : ℕ) (h : CN'zFix N) (D : CongruentDissection N) : False :=
  not_tile_of_conditionsNSQzFixx N _
    (fun hS1 => Erdos634.Draft.S1Band.s1ubClosed_of_free N (Erdos634.Draft.S1Band.s1ubFree_of_W hS1))
    (cnzFixx_of_Fix h) D

theorem not_tileCount_of_conditionsNSQzFix (N : ℕ) (h : CN'zFix N) : ¬ Nonempty (CongruentDissection N) :=
  fun ⟨D⟩ => not_tile_of_conditionsNSQzFix N h D

end Erdos634.Draft.NSQM

#print axioms Erdos634.Draft.NSQM.not_tile_of_conditionsNSQzFix
#print axioms Erdos634.Draft.NSQM.not_tileCount_of_conditionsNSQzFix
