/-
Draft/NSQMMainZETWD3.lean -- `CN'zETWD3` = `CN'zETWD2` with (i) the A leaf `EllChk2 N` replaced by `EllChk2 N ∨ AsqChk N`, where
`AsqChk N` is `N = 15 s^2` or `N = 30 s^2` (`GAU.gapA_sq`, `GapA N` directly: no dissection with all angles in Q*pi), and (ii) the S1 leaf `S1Chk N`
replaced by `S1t2Chk N` (`NSQS1T2`: `2 t p < q`, plus the equality instance `T_t(1,2t)`, `no_dissection_T_half`).  Existing modules untouched.
`not_tile_of_conditionsNSQzETWD3 : CN'zETWD3 N -> CongruentDissection N -> False`.  the census program increments: 85 values 30 s^2 (A only), 6 values M^2(12M^2-1).  The G-leaf formal input is `ThmD.thmDStatement_geo`
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
import Erdos634.Draft.NSQMMainZETWD2
import Erdos634.Draft.GAUFinal
import Erdos634.Draft.NSQS1T2

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

def AsqChk (N : ℕ) : Prop := ∃ s, s ≤ N ∧ 0 < s ∧ (N = 15 * (s * s) ∨ N = 30 * (s * s))

instance (N : ℕ) : Decidable (AsqChk N) := by unfold AsqChk; infer_instance

def CN'zETWD3 (N : ℕ) : Prop :=
  NQChk N ∧ (EllChk2 N ∨ AsqChk N) ∧ LeafNSq N ∧ LeafHAr N ∧ LeafR N ∧ LeafEsqN N ∧ LeafF1p N ∧ LeafS2 N ∧ LeafS3 N ∧ LeafIso N ∧
    LeafR8z N ∧ Erdos634.Draft.ThmD.GammaChkD N ∧ Erdos634.Draft.NSQS1T2.S1t2Chk N ∧ RWChkT2 N ∧ S5wChk N

instance (N : ℕ) : Decidable (CN'zETWD3 N) := by unfold CN'zETWD3; infer_instance

/-- **The final chain with the S+ kill in the S4 leaf (`RWChkT2`).** -/
theorem not_tile_of_conditionsNSQzETWD3 (N : ℕ) (h : CN'zETWD3 N) (D : CongruentDissection N) : False := by
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
  refine chain_nsq N (Erdos634.Draft.NSQS1T2.s1t2Closed_of_free N (Erdos634.Draft.NSQS1T2.s1t2Free_of_chk hS1))
    (s2Closed_of_arith N (s2Arith_of_chk hN0 hS2))
    (s3Closed_of_isoQRef N (isoQRef_of_chk hN0 hS3))
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
    · exact gapE120_of_chk hN0 h120
  · rcases hF1 with h4 | hf
    · exact gapF1_of_mod4_two N h4
    · exact gapF1_of_chkpar (by omega) hf

end Erdos634.Draft.NSQM

#print axioms Erdos634.Draft.NSQM.not_tile_of_conditionsNSQzETWD3
