/-
Draft/LeafFixIsoChain.lean -- `CN'zFixIso N`: the chain `CN'zFix` (LeafFixChain) with the Iso conjunct `IsoH9bChkW N` REPLACED by the ISO-INT leaf `IsoH9cChkW N`.
  Iso: `IsoH9bChkW N` -> `IsoH9cChkW N` (LeafFixIsoChk: `IsoBad` plus `b | k`; closure `isoH9c_of_chk` from `LeafFixIsoThm.thmIso_H9c`, which keeps both `cor:int` parities).
  Every other conjunct is textually identical to `CN'zFix`.
`chain_nsq_c` = COPY of `NSQMain.chain_nsq` (lines 37-91) with `hH : IsoH9b N` -> `IsoH9c N` and `thmIso_H9b` -> `thmIso_H9c`.
The bodies of `not_tile_of_conditionsNSQzFixIsox`, `CN'zFixIso` etc. are COPIED from LeafFixChain.lean (lines 33-106) with the renames above.
Credit: Beeson-Rosu (cor:int, flux invariants), Laczkovich, Paliy.  STRENGTH: internal audit only; UNAUDITED (this module).  Not imported by any aggregate.  No sorry, no native_decide.
-/
import Erdos634.Draft.LeafFixChain
import Erdos634.Draft.LeafFixIsoChk

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
open Erdos634.Draft.LeafFixIso

/-- The dispatch of `chain_gen3` with the squarefree leaves (S1, S4, S5, γ = 2α, Case A/B) abstracted as hypotheses. -/
theorem chain_nsq_c (N : ℕ)
    (gS1 : S1Closed N) (gS2 : S2Closed N) (gS3 : S3Closed N) (hH : IsoH9c N)
    (gS4 : RWStatementNsq N) (gS5 : RAStatementNsq N)
    (gA : GapAcomp N) (gB : CaseBClosed N) (gR : CaseRClosed N) (gG : CaseGClosed N)
    (gE60 : GapE60 N) (gE120 : GapE120 N) (gF1 : GapF1 N) (gR8 : GapR8 N)
    (D : CongruentDissection N) : False := by
  -- Case A (Lemma S is proved, N-free, and supplied)
  by_cases hA : ∀ k, ∃ q : ℚ, D.model.angleAt k = q * Real.pi
  · exact gA Erdos634.LemmaSAll.lemmaS D hA
  have hirr : ∃ k, IrrPi (D.model.angleAt k) := by
    by_contra hc
    exact hA fun k => by_contra fun hk => hc ⟨k, hk⟩
  -- Case B
  by_cases hB : SimilarTM D
  · obtain ⟨μ, τ, hs⟩ := hB
    exact gB D μ τ hs
  -- Case C
  rcases Erdos634.Draft.LemmaCFinal.lemmaC_general D hirr hB with hR | hT | hS | hTP | h32
  · exact gR D hR
  · obtain ⟨α, a, b, c, hα, hd, i, j, hij, hi, hj⟩ := hT
    exact gG D α a b c hα hd i j hij hi hj
  · obtain ⟨α, a, b, c, hα, hd⟩ := hS
    exact gE60 D α a b c hα hd (Erdos634.Draft.LemmaPProof.lemmaP_general D α a b c hα hd hB)
  · obtain ⟨α, a, b, c, hα, hd, hsh⟩ := hTP
    rcases hsh with he | hi | hf | hr
    · exact gE120 D α a b c hα hd he
    · exact Erdos634.Draft.LeafFixIso.thmIso_H9c N D hH α a b c hα hd hi
    · exact gF1 D α a b c hα hd hf
    · exact gR8 D α a b c hα hd hr
  · obtain ⟨α, β, a, b, c, hα, hrel, hd, hsh⟩ := h32
    obtain ⟨σ, m0, o0, m1, o1, m2, o2⟩ := id hd
    have s01 : σ 0 ≠ σ 1 := σ.injective.ne (by decide)
    have s20 : σ 2 ≠ σ 0 := σ.injective.ne (by decide)
    have s21 : σ 2 ≠ σ 1 := σ.injective.ne (by decide)
    rcases hsh with ⟨τ, t0, t1, t2⟩ | ⟨τ, t0, t1, t2⟩ | ⟨τ, t0, t1, t2⟩ | ⟨τ, t0, t1, t2⟩ |
        ⟨τ, t0, t1, t2⟩
    · obtain ⟨r, hr, hb⟩ := Row12.rational_any_label D hα hrel hd
        (τ.injective.ne (by decide : (0 : Fin 3) ≠ 1)) t0 t1
      exact gS1 D α β a b c r hα hrel hd hr hb ⟨τ, t0, t1, t2⟩
    · obtain ⟨r, hr, hb⟩ := Row13.rational_any_label D hα hrel hd
        (τ.injective.ne (by decide : (0 : Fin 3) ≠ 1)) t0 t1
      exact not_baseBetaTiled (gS5 D α β a b c r hα hrel hd hr hb ⟨τ, t0, t1, t2⟩)
    · obtain ⟨r, hr⟩ := Row14.rational_any_label D α β hα hrel s01 s20 s21 m0 m1
        (τ.injective.ne (by decide : (0 : Fin 3) ≠ 1)) t0 t1
      rw [o0, o2] at hr
      exact not_baseBetaTiled (gS4 D α β a b c r hα hrel hd hr
        (Rows11_13AnyLabel.b_of_rational hrel hd hr) ⟨τ, t0, t1, t2⟩)
    · obtain ⟨r, hr, -⟩ := Row15.rational_any_label D α β hα hrel s01 s20 s21 m0 m1
        (τ.injective.ne (by decide : (0 : Fin 3) ≠ 1)) t0 t1
      rw [o0, o2] at hr
      exact gS2 D α β a b c r hα hrel hd hr
        (Rows11_13AnyLabel.b_of_rational hrel hd hr) ⟨τ, t0, t1, t2⟩
    · exact gS3 D α β a b c hα hrel hd (τ 0) (τ 1)
        (τ.injective.ne (by decide : (0 : Fin 3) ≠ 1)) t0 t1

def CN'zFixIsox (N : ℕ) (S : Prop) : Prop :=
  NQChk N ∧ (EllChk2 N ∨ AsqChk N) ∧ LeafNSq N ∧ LeafHAr N ∧ LeafR N ∧ LeafEsqS N ∧ LeafF1p N ∧ LeafS2 N ∧ S3newChk N ∧ IsoH9cChk N ∧
    LeafR8z N ∧ Erdos634.Draft.ThmD.GammaChkD N ∧ S ∧ RWChkT2 N ∧ S5wChk N

theorem not_tile_of_conditionsNSQzFixIsox (N : ℕ) (S : Prop) (hcl : S → S1Closed N) (h : CN'zFixIsox N S)
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
  refine chain_nsq_c N (hcl hS1)
    (s2Closed_of_arith N (s2Arith_of_chk hN0 hS2))
    (s3Closed_of_fix N hN0 hS3)
    (isoH9c_of_chk hN0 hIso)
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
def CN'zFixIso (N : ℕ) : Prop :=
  NQChkW N ∧ (EllChk2 N ∨ AsqChk N) ∧ NSqChkSq N ∧ HArithChkSq N ∧
    (N % 2 = 1 ∨ (N % 2 = 0 ∧ NHSqChkSq N)) ∧ LeafEsqS N ∧ (N % 4 = 2 ∨ F1ChkParW N) ∧ S2ChkSq N ∧ S3newChk N ∧ IsoH9cChkW N ∧
    (NoF2ChkSq N ∧ NoF3zChkSq N ∧ NoF4zChkSq N) ∧ GammaChkDW N ∧ Erdos634.Draft.S1Band.S1UBChkW N ∧ RWChkT2W N ∧ S5wChkW N

instance (N : ℕ) : Decidable (CN'zFixIso N) := by unfold CN'zFixIso; infer_instance

theorem cnzFixIsox_of_Fix {N : ℕ} (h : CN'zFixIso N) : CN'zFixIsox N (Erdos634.Draft.S1Band.S1UBChkW N) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, ⟨a, b, c⟩, h12, h13, h14, h15⟩ := h
  refine ⟨nqChk_of_W h1, h2, nsqChk_of_sq h3, hArithChk_of_sq h4, ?_, h6, ?_, s2Chk_of_sq h8, h9,
    isoH9cChk_of_W h10, ⟨noF2Chk_of_sq a, noF3zChk_of_sq b, noF4zChk_of_sq c⟩, gammaChkD_of_W h12, h13,
    rwChkT2_of_W h14, s5wChk_of_W h15⟩
  · rcases h5 with h | ⟨h, h'⟩
    · exact Or.inl h
    · exact Or.inr ⟨h, nhsqChk_of_sq h'⟩
  · rcases h7 with h | h
    · exact Or.inl h
    · exact Or.inr (f1ChkPar_of_W h)

/-- **The final chain with the corrected S3 and E leaves.**  Conclusion identical to `not_tile_of_conditionsNSQzUB`. -/
theorem not_tile_of_conditionsNSQzFixIso (N : ℕ) (h : CN'zFixIso N) (D : CongruentDissection N) : False :=
  not_tile_of_conditionsNSQzFixIsox N _
    (fun hS1 => Erdos634.Draft.S1Band.s1ubClosed_of_free N (Erdos634.Draft.S1Band.s1ubFree_of_W hS1))
    (cnzFixIsox_of_Fix h) D

theorem not_tileCount_of_conditionsNSQzFixIso (N : ℕ) (h : CN'zFixIso N) : ¬ Nonempty (CongruentDissection N) :=
  fun ⟨D⟩ => not_tile_of_conditionsNSQzFixIso N h D


end Erdos634.Draft.NSQM

#print axioms Erdos634.Draft.NSQM.not_tile_of_conditionsNSQzFixIso
#print axioms Erdos634.Draft.NSQM.not_tileCount_of_conditionsNSQzFixIso
