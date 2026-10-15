/-
Draft/NSQMain.lean — THE NON-SQUAREFREE ALL-N THEOREM.

    theorem not_tile_of_nsq (N : ℕ) (h : CN N) (D : CongruentDissection N) : False

`CN N` is a conjunction of DECIDABLE bounded arithmetic checks.  It differs from `AllN2Cond.C'` exactly where `C'` used `Squarefree N`:
  Sqf+Range+Ell  →  `NQChk N` (N = s² n, n squarefree, 7 ≤ n, 17 ≤ n or n ≡ 2,3 mod 4 : Case B / Case A exit, `NSQCaseB`/`NSQCaseA`)
                    and `EllChk2 N` (a prime ℓ ≥ 7 with ℓ ∣ N, ℓ² ∤ N : Lemma V)
  γ = 2α            →  `GammaChk N`   (`NSQLegs`: gcd((M'−M)/2, N) = 1 for all N = M M' in the γ=2α range)
  S1                →  `S1Chk N`      (`NSQS1`: no t ≥ 2 with N = t² (3q²−p²))
  S4 (R-W)          →  `RWChk N`      (`NSQRW`: no S' ≥ 2 with N = S'² (2f²−e²))
  S5 (R-A)          →  `RAShape N`    (`NSQRA`: N squarefree or N = 8 m, m odd squarefree, which gives `N ∣ (f−e) K`)
  F1                →  `F1ChkPar`-form (`NSQF1`/`NSQChk`: parity of `cor_int`)
and keeps every N-general leaf of `C'` (NSq, HAr, R, E' (π/3 and 2π/3 pair tables), S2, S3, Iso, R8).
For squarefree N it is NOT weaker than C' on the new leaves; the theorem is aimed at NON-squarefree N:
`CN 152` (152 = 8·19) holds by `decide +kernel`.  No sorry, no native_decide.
-/
import Erdos634.Draft.AllN2Cond
import Erdos634.Draft.NSQCaseA
import Erdos634.Draft.NSQRADvd
import Erdos634.Draft.NSQChk
import Erdos634.Draft.NSQGammaChk

set_option maxRecDepth 8000
set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000

namespace Erdos634.Draft.NSQMain

open Erdos634.Geometry Erdos634.Draft.TheoremPConditional Erdos634.Draft.Chain15 Erdos634.Draft.ChainComposite
open Erdos634.Draft.CompositeGen2 Erdos634.Draft.CompositeArith Erdos634.Draft.CompositeS2Arith
open Erdos634.Draft.CompositeS1Arith Erdos634.Draft.CompositeIsoB Erdos634.Draft.CompositeFinal2
open Erdos634.Draft.CompositeFinal3 Erdos634.Draft.AllNExclusion Erdos634.Draft.AllN2
open Erdos634.Draft.NSQRA Erdos634.Draft.NSQRW Erdos634.Draft.NSQS1 Erdos634.Draft.NSQChk Erdos634.Draft.NSQLegs

/-- The dispatch of `chain_gen3` with the squarefree leaves (S1, S4, S5, γ = 2α, Case A/B) abstracted as hypotheses. -/
theorem chain_nsq (N : ℕ)
    (gS1 : S1Closed N) (gS2 : S2Closed N) (gS3 : S3Closed N) (hH : IsoH9b N)
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
    · exact Erdos634.Draft.ThmIsoH9b.thmIso_H9b N D hH α a b c hα hd hi
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



/-! ## The conditions -/

def NQChk (N : ℕ) : Prop :=
  ∃ s ≤ N, ∃ n ≤ N, 0 < s ∧ Squarefree n ∧ N = s ^ 2 * n ∧ 7 ≤ n ∧ (17 ≤ n ∨ n % 4 = 2 ∨ n % 4 = 3)

instance (N : ℕ) : Decidable (NQChk N) := by unfold NQChk; infer_instance

theorem nq_of_chk {N : ℕ} (h : NQChk N) : Erdos634.Geometry.NQ N := by
  obtain ⟨s, -, n, -, h0, hn, hN, h7, hQ⟩ := h
  exact ⟨s, n, h0, hn, hN, h7, hQ⟩

/-- A prime `ℓ ≥ 7` with `ℓ ∣ N`, `ℓ² ∤ N` (valuation exactly 1; odd). -/
def EllChk2 (N : ℕ) : Prop :=
  ∃ ℓ ≤ N, 7 ≤ ℓ ∧ ℓ ∣ N ∧ ¬ ℓ * ℓ ∣ N ∧ ∀ m < ℓ, m ∣ ℓ → m = 1

instance (N : ℕ) : Decidable (EllChk2 N) := by unfold EllChk2; infer_instance

theorem ell_of_chk2 {N : ℕ} (h : EllChk2 N) :
    ∃ ℓ : ℕ, ℓ.Prime ∧ 7 ≤ ℓ ∧ ¬ Even (padicValNat ℓ N) := by
  obtain ⟨ℓ, -, h7, hd, hnd2, hp⟩ := h
  have hpr : ℓ.Prime := Nat.prime_def_lt.mpr ⟨by omega, hp⟩
  refine ⟨ℓ, hpr, h7, ?_⟩
  obtain ⟨k, hk⟩ := hd
  have hk0 : k ≠ 0 := by
    rintro rfl
    simp at hk; subst hk; exact hnd2 (dvd_zero _)
  have hnd : ¬ ℓ ∣ k := by
    rintro ⟨k', rfl⟩
    exact hnd2 ⟨k', by rw [hk]; ring⟩
  rw [hk]
  exact notEven_of_odd (val_one hpr hnd hk0)

/-- The shape for which the R-A arithmetic `RADvd N` is proved: `N` squarefree, or `N = 8 m`, `m` odd squarefree. -/
def RAShape (N : ℕ) : Prop := Squarefree N ∨ (N % 8 = 0 ∧ Squarefree (N / 8) ∧ (N / 8) % 2 = 1)

instance (N : ℕ) : Decidable (RAShape N) := by unfold RAShape; infer_instance

theorem radvd_of_shape {N : ℕ} (h : RAShape N) : RADvd N := by
  rcases h with h | ⟨h8, hsq, hodd⟩
  · exact ra_dvd_of_squarefree h
  · have := ra_dvd_of_eight (N / 8) hsq hodd
    have e : 8 * (N / 8) = N := by omega
    rwa [e] at this

def LeafF1p (N : ℕ) : Prop := N % 4 = 2 ∨ F1ChkPar N

instance (N : ℕ) : Decidable (LeafF1p N) := by unfold LeafF1p; infer_instance

/-- **The condition `CN N`.** -/
def CN (N : ℕ) : Prop :=
  NQChk N ∧ EllChk2 N ∧ LeafNSq N ∧ LeafHAr N ∧ LeafR N ∧ LeafE' N ∧ LeafF1p N ∧ LeafS2 N ∧ LeafS3 N ∧ LeafIso N ∧
    LeafR8 N ∧ GammaChk N ∧ S1Chk N ∧ RWChk N ∧ RAShape N

instance (N : ℕ) : Decidable (CN N) := by unfold CN; infer_instance

/-- **The non-squarefree all-N theorem.**  No `N` satisfying the decidable arithmetic conditions `CN N` is a tile count. -/
theorem not_tile_of_nsq (N : ℕ) (h : CN N) (D : CongruentDissection N) : False := by
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
    (rwStatement_nsq N (rwFree_of_chk hRW)) (raStatement_nsq N (radvd_of_shape hRA))
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

end Erdos634.Draft.NSQMain

#print axioms Erdos634.Draft.NSQMain.chain_nsq
#print axioms Erdos634.Draft.NSQMain.not_tile_of_nsq
