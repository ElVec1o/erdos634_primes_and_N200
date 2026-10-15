/-
Draft/CompositeN60.lean -- N = 60 = 4*3*5 (NOT squarefree): the strongest chain this corpus supports, with the non-squarefree leaves
as NAMED hypotheses.  `chain_60_final` has residual hypotheses
    GapA 60            Case A (rational angles) at N = 60
    CaseBClosed 60     target similar to tile (Lemma Q / SWW at non-squarefree N: Row2.lemmaQ needs Squarefree N)
    CaseGClosed 60     gamma = 2 alpha (N % 4 = 0: Row4.not_two_mod_four and Row4.not_squarefree both inapplicable)
    GapE60 60, GapE120 60, GapF1 60, GapR8 60   (parity trick fails: 60 % 4 = 0; NoF3 60 is FALSE: 8*10 = 80 = 240/3)
    RA60, RW60         S5 / S4 (RASquarefree / RWSquarefree need Squarefree N)
  Discharged here: Right (H1k.h1Right 60, 30 not x^2+y^2), S1 (l = 5), S2 (l = 5), S3 (IsoQRef 60 by check), IsoH9 60 by check.
  CONDITIONAL on EIGHT leaves; NOT an exclusion of 60.  No sorry, no native_decide. ***
-/
import Erdos634.Draft.CompositeN30
import Erdos634.Draft.RASquarefree
import Erdos634.Draft.RWSquarefree

open scoped Classical

set_option synthInstance.maxSize 1000
set_option synthInstance.maxHeartbeats 400000

namespace Erdos634.Draft.CompositeN60

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.Draft.TheoremPConditional Erdos634.Draft.Chain15 Erdos634.Draft.ChainComposite
open Erdos634.Draft.CompositeGen2 Erdos634.Draft.CompositeArith Erdos634.Draft.CompositeFinal2

def RA60 : Prop :=
  ∀ (D : CongruentDissection 60) (α β a b c : ℝ) (r : ℚ), IrrPi α → 3 * α + 2 * β = Real.pi →
    D.model.ThreeAlphaData α β a b c → a = (r : ℝ) * c → b = (1 - (r : ℝ) ^ 2) * c →
    TgtAngles D (α + β) (α + β) α → BaseBetaTiled

def RW60 : Prop :=
  ∀ (D : CongruentDissection 60) (α β a b c : ℝ) (r : ℚ), IrrPi α → 3 * α + 2 * β = Real.pi →
    D.model.ThreeAlphaData α β a b c → a = (r : ℝ) * c → b = (1 - (r : ℝ) ^ 2) * c →
    TgtAngles D (2 * α) β (α + β) → BaseBetaTiled

theorem isoH9_60 : IsoH9 60 := isoH9_of_check 60 (by norm_num) (by decide +kernel)
theorem isoQRef_60 : IsoQRef 60 := isoQRef_of_check 60 (by norm_num) (by norm_num) (by decide +kernel)
theorem nsqh60 : ¬ ∃ x y : ℕ, 60 = 2 * (x ^ 2 + y ^ 2) := nsq_half 60 (by norm_num) (by decide)

theorem val5_60 : Odd (padicValNat 5 60) := val_one (p := 5) (k := 12) (by norm_num) (by norm_num) (by norm_num)

theorem chain_60_final (gA : GapA 60) (gB : CaseBClosed 60) (gG : CaseGClosed 60)
    (gE60 : GapE60 60) (gE120 : GapE120 60) (gF1 : GapF1 60) (gR8 : GapR8 60)
    (gRA : RA60) (gRW : RW60) (D : CongruentDissection 60) : False := by
  have gR : CaseRClosed 60 := caseR_of_H1 60 (Erdos634.Draft.H1k.h1Right 60) nsqh60
  have gS2 : S2Closed 60 := s2Closed_of_qnr 60 5 (by norm_num) val5_60 qnr2_5 qnr3_5
  have gS3 : S3Closed 60 := s3Closed_of_isoQRef 60 isoQRef_60
  by_cases hA : ∀ k, ∃ q : ℚ, D.model.angleAt k = q * Real.pi
  · exact gA D hA
  have hirr : ∃ k, IrrPi (D.model.angleAt k) := by
    by_contra hc
    exact hA fun k => by_contra fun hk => hc ⟨k, hk⟩
  by_cases hB : SimilarTM D
  · obtain ⟨μ, τ, hs⟩ := hB
    exact gB D μ τ hs
  rcases Erdos634.Draft.LemmaCFinal.lemmaC_general D hirr hB with hR | hT | hS | hTP | h32
  · exact gR D hR
  · obtain ⟨α, a, b, c, hα, hd, i, j, hij, hi, hj⟩ := hT
    exact gG D α a b c hα hd i j hij hi hj
  · obtain ⟨α, a, b, c, hα, hd⟩ := hS
    exact gE60 D α a b c hα hd (Erdos634.Draft.LemmaPProof.lemmaP_general D α a b c hα hd hB)
  · obtain ⟨α, a, b, c, hα, hd, hsh⟩ := hTP
    rcases hsh with he | hi | hf | hr
    · exact gE120 D α a b c hα hd he
    · exact Erdos634.Draft.ThmIsoH9.thmIso_H9 60 D isoH9_60 α a b c hα hd hi
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
      exact Erdos634.Draft.ScaleBaseBetaQNR.scaleBaseBeta_qnr 60 D 5 (by norm_num) val5_60 qnr3_5
        α β a b c r hα hrel hd hr hb ⟨τ, t0, t1, t2⟩
    · obtain ⟨r, hr, hb⟩ := Row13.rational_any_label D hα hrel hd
        (τ.injective.ne (by decide : (0 : Fin 3) ≠ 1)) t0 t1
      exact not_baseBetaTiled (gRA D α β a b c r hα hrel hd hr hb ⟨τ, t0, t1, t2⟩)
    · obtain ⟨r, hr⟩ := Row14.rational_any_label D α β hα hrel s01 s20 s21 m0 m1
        (τ.injective.ne (by decide : (0 : Fin 3) ≠ 1)) t0 t1
      rw [o0, o2] at hr
      exact not_baseBetaTiled (gRW D α β a b c r hα hrel hd hr
        (Rows11_13AnyLabel.b_of_rational hrel hd hr) ⟨τ, t0, t1, t2⟩)
    · obtain ⟨r, hr, -⟩ := Row15.rational_any_label D α β hα hrel s01 s20 s21 m0 m1
        (τ.injective.ne (by decide : (0 : Fin 3) ≠ 1)) t0 t1
      rw [o0, o2] at hr
      exact gS2 D α β a b c r hα hrel hd hr
        (Rows11_13AnyLabel.b_of_rational hrel hd hr) ⟨τ, t0, t1, t2⟩
    · exact gS3 D α β a b c hα hrel hd (τ 0) (τ 1)
        (τ.injective.ne (by decide : (0 : Fin 3) ≠ 1)) t0 t1

end Erdos634.Draft.CompositeN60

#print axioms Erdos634.Draft.CompositeN60.chain_60_final
