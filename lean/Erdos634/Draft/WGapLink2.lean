/-
Draft/WGapLink2.lean -- 16 November 2026 (work item internal working notes).  UNAUDITED beyond internal checks.  Not imported by any aggregate.  Leaf module.
The census decision rule for the W-gap values as ONE Lean theorem (task T13 of G3_SCOPE.md, link 13):
* `RWChkW N` (decidable, windowed like `RWChkT2W`): no representation `N = s^2 (2 f^2 - e^2)`, `s >= 2`, `0 < e < f` coprime, with `f <= s e` (else `SideRunG.not_wTilable_ebelow`)
  that is OUTSIDE the W-gap window `2 <= e /\ s (f - e) < f` (else `WGapRung.no_tiling_W_gap`).  `rwFreeW_of_chk : RWChkW N -> RWFreeW N` (WGapLink1).
* `CNzFixW N` = `CN'zFix N` (LeafFixChain.lean:79) with `RWChkT2W N` replaced by `RWChkW N`; all other 14 conjuncts textually identical.
* `not_tile_of_CNzFixW`, `not_tileCount_of_CNzFixW : CNzFixW N -> not TileCount N` (`TileCountFamilies.TileCount N := Nonempty (CongruentDissection N)`).
  The body is the body of `not_tile_of_conditionsNSQzFixx` (LeafFixChain.lean:50-77) COPIED (that file is untouched); the only change is the S4 leaf:
  `rwStatement_nsqW N (rwFreeW_of_chk hRW)` instead of `rwStatement_nsqT2 N (rwFreeT2_of_chk hRW)`.
* `rwChkW_of_T2W : RWChkT2W N -> RWChkW N` (so `CN'zFix N -> CNzFixW N`: the new rule only extends the closures; control).
Credit: Beeson-Rosu, Paliy, the S+ work item, Laczkovich (band), Zhang.  No sorry, no native_decide.
-/
import Erdos634.Draft.WGapLink1
import Erdos634.Draft.LeafFixChain
import Erdos634.Draft.TileCountFamilies

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
open Erdos634.Draft.WGapLink1

/-- the S4 check with the W-gap window (windowed like `RWChkT2W`) -/
def RWChkW (N : ℕ) : Prop :=
  ∀ s ≤ Nat.sqrt N, 2 ≤ s → s * s ∣ N → ∀ f ≤ Nat.sqrt (N / (s * s)), N / (s * s) ≤ 2 * f * f →
    ¬ (sqChk (2 * f * f - N / (s * s)) ∧ 0 < Nat.sqrt (2 * f * f - N / (s * s)) ∧
       Nat.sqrt (2 * f * f - N / (s * s)) < f ∧ Nat.Coprime (Nat.sqrt (2 * f * f - N / (s * s))) f ∧
       f ≤ s * Nat.sqrt (2 * f * f - N / (s * s)) ∧
       ¬ (2 ≤ Nat.sqrt (2 * f * f - N / (s * s)) ∧ s * (f - Nat.sqrt (2 * f * f - N / (s * s))) < f))

instance (N : ℕ) : Decidable (RWChkW N) := by unfold RWChkW sqChk; infer_instance

theorem rwFreeW_of_chk {N : ℕ} (h : RWChkW N) : RWFreeW N := by
  intro M e f he hef hcop hM hN hfM hng
  have hM2 : 2 ≤ M := by
    by_contra hlt
    have h1 : M = 1 := by omega
    subst h1
    omega
  have h2 : 2 * f ^ 2 - e ^ 2 = 2 * f * f - e * e := by simp [pow_two, mul_assoc]
  have hN' : N = M * M * (2 * f * f - e * e) := by
    rw [hN, h2, pow_two, Nat.mul_comm]
  have hee : e * e < f * f := Nat.mul_self_lt_mul_self hef
  have hff : f ≤ f * f := Nat.le_mul_self f
  have hYpos : 0 < 2 * f * f - e * e := by
    apply Nat.sub_pos_of_lt; nlinarith
  have hdiv : N / (M * M) = 2 * f * f - e * e := by
    rw [hN']; exact Nat.mul_div_cancel_left _ (by positivity)
  have hss : M * M ∣ N := ⟨_, hN'⟩
  have hMN : M * M ≤ N := by rw [hN']; exact Nat.le_mul_of_pos_right _ hYpos
  have hMs : M ≤ Nat.sqrt N := Nat.le_sqrt.mpr hMN
  have hfs : f ≤ Nat.sqrt (N / (M * M)) := by
    apply Nat.le_sqrt.mpr; rw [hdiv]
    have e2 : 2 * f * f = 2 * (f * f) := by ring
    omega
  have hle2 : N / (M * M) ≤ 2 * f * f := by rw [hdiv]; omega
  have hsub : 2 * f * f - N / (M * M) = e * e := by rw [hdiv]; omega
  apply h M hMs hM2 hss f hfs hle2
  rw [hsub, Nat.sqrt_eq]
  exact ⟨by unfold sqChk; rw [Nat.sqrt_eq], he, hef, hcop, hfM, hng⟩

theorem w_arith (s e f : ℕ) (h2e : 2 ≤ e) (hef : e < f) (hsf : s < f) (hk : s * (f - e) ≤ e + 1) :
    s * (f - e) < f := by
  rcases Nat.lt_or_ge (e + 1) f with h | h
  · omega
  · have h1 : f - e = 1 := by omega
    rw [h1, Nat.mul_one]; exact hsf

/-- control: the old windowed S4 check implies the new one, so `CN'zFix N -> CNzFixW N` -/
theorem rwChkW_of_T2W {N : ℕ} (h : RWChkT2W N) : RWChkW N := by
  intro s hs h2 hd f hf hn hb
  obtain ⟨hsq, he0, hef, hcop, hfs, hng⟩ := hb
  apply h s hs h2 hd f hf hn
  refine ⟨hsq, he0, hef, hcop, hfs, ?_, ?_⟩
  · -- e < s (f - e): else s (f - e) <= e, and then (2 <= e, s (f-e) < f) holds, contradiction with hng
    by_contra hcon
    push Not at hcon
    apply hng
    refine ⟨?_, ?_⟩
    · by_contra h2e; push Not at h2e
      have he1 : Nat.sqrt (2 * f * f - N / (s * s)) = 1 := by omega
      rw [he1] at hcon
      have : 1 ≤ f - 1 := by omega
      nlinarith
    · have : 0 < f - Nat.sqrt (2 * f * f - N / (s * s)) := by omega
      have := Nat.lt_of_le_of_lt hcon hef
      exact this
  · rintro ⟨h2e, hsf, hk⟩
    apply hng
    refine ⟨h2e, ?_⟩
    exact w_arith s _ f h2e hef hsf hk

def CNzFixW (N : ℕ) : Prop :=
  NQChkW N ∧ (EllChk2 N ∨ AsqChk N) ∧ NSqChkSq N ∧ HArithChkSq N ∧
    (N % 2 = 1 ∨ (N % 2 = 0 ∧ NHSqChkSq N)) ∧ LeafEsqS N ∧ (N % 4 = 2 ∨ F1ChkParW N) ∧ S2ChkSq N ∧ S3newChk N ∧ IsoH9bChkW N ∧
    (NoF2ChkSq N ∧ NoF3zChkSq N ∧ NoF4zChkSq N) ∧ GammaChkDW N ∧ Erdos634.Draft.S1Band.S1UBChkW N ∧ RWChkW N ∧ S5wChkW N

instance (N : ℕ) : Decidable (CNzFixW N) := by unfold CNzFixW; infer_instance

theorem cnzFixW_of_Fix {N : ℕ} (h : CN'zFix N) : CNzFixW N := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, rwChkW_of_T2W h14, h15⟩

theorem not_tile_of_CNzFixW (N : ℕ) (h : CNzFixW N) (D : CongruentDissection N) : False := by
  obtain ⟨h1, hEll, h3, h4, h5, hE, h7, h8, hS3, h10, ⟨a, b, c⟩, h12, h13, h14, hRA'⟩ := h
  have hNQ : NQChk N := nqChk_of_W h1
  have hNSq : NSqChk N := nsqChk_of_sq h3
  have hHAr : HArithChk N := hArithChk_of_sq h4
  have hR : N % 2 = 1 ∨ (N % 2 = 0 ∧ NHSqChk N) := by
    rcases h5 with h | ⟨h, h'⟩
    · exact Or.inl h
    · exact Or.inr ⟨h, nhsqChk_of_sq h'⟩
  have hF1 : N % 4 = 2 ∨ F1ChkPar N := by
    rcases h7 with h | h
    · exact Or.inl h
    · exact Or.inr (f1ChkPar_of_W h)
  have hS2 : S2Chk N := s2Chk_of_sq h8
  have hIso : IsoH9bChk N := isoH9bChk_of_W h10
  have hF2c : NoF2Chk N := noF2Chk_of_sq a
  have hF3c : NoF3zChk N := noF3zChk_of_sq b
  have hF4c : NoF4zChk N := noF4zChk_of_sq c
  have hG : Erdos634.Draft.ThmD.GammaChkD N := gammaChkD_of_W h12
  have hRA : S5wChk N := s5wChk_of_W hRA'
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
  refine chain_nsq N (Erdos634.Draft.S1Band.s1ubClosed_of_free N (Erdos634.Draft.S1Band.s1ubFree_of_W h13))
    (s2Closed_of_arith N (s2Arith_of_chk hN0 hS2))
    (s3Closed_of_fix N hN0 hS3)
    (isoH9b_of_chk hN0 hIso)
    (rwStatement_nsqW N (rwFreeW_of_chk h14)) (raStatement_of_s5w N hRA)
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

/-- **The census decision rule for the W-gap values, as one theorem.**  Conclusion: `N` is not a tile count (`TileCount N := Nonempty (CongruentDissection N)`). -/
theorem not_tileCount_of_CNzFixW (N : ℕ) (h : CNzFixW N) : ¬ Erdos634.Draft.TileCountFamilies.TileCount N :=
  fun ⟨D⟩ => not_tile_of_CNzFixW N h D

end Erdos634.Draft.NSQM

#print axioms Erdos634.Draft.NSQM.rwFreeW_of_chk
#print axioms Erdos634.Draft.NSQM.rwChkW_of_T2W
#print axioms Erdos634.Draft.NSQM.cnzFixW_of_Fix
#print axioms Erdos634.Draft.NSQM.not_tile_of_CNzFixW
#print axioms Erdos634.Draft.NSQM.not_tileCount_of_CNzFixW
