import Erdos634.Draft.ThmDStmt2
import Erdos634.Draft.ThmDStatementGeo
import Erdos634.Draft.ThmDLeaf
import Erdos634.Draft.NSQMMainZET

/-!
Credit: the method (rigidity window, Lemmas 30-34, row induction, Theorem 37) is adapted from M. Beeson and G. Rosu, 'Tiling a triangle into a prime number of congruent triangles' (preprint, 16 Oct 2026); the transfer to the tile with gamma = 2 alpha (fan lemma at straight points, windows u and v, Lemma K) is ours. Here: the counting along a leg (the final counting of their Theorem 37 is the model).
# Theorem D': the chain theorem `CN'zETD`  (; unconditional since `thmDStatement_geo`)

`CN'zETD` is `CN'zET` with the G leaf `GammaChk` replaced by `GammaChkD` (which also accepts the pairs of Theorem D').
`not_tile_of_conditionsNSQzETD` : `CN'zETD N -> no N-tiling` (uses `ThmD.thmDStatement_geo`).  The ONLY change to the proof of
`not_tile_of_conditionsNSQzET` is the closure of the G case: `caseG_of_gammaChkD` instead of `caseG_of_gammaArith`.


-/

namespace Erdos634.Draft.NSQM

open Erdos634.Geometry Erdos634.Draft.TheoremPConditional Erdos634.Draft.Chain15 Erdos634.Draft.ChainComposite
open Erdos634.Draft.CompositeGen2 Erdos634.Draft.CompositeArith Erdos634.Draft.CompositeS2Arith
open Erdos634.Draft.CompositeS1Arith Erdos634.Draft.CompositeIsoB Erdos634.Draft.CompositeFinal2
open Erdos634.Draft.CompositeFinal3 Erdos634.Draft.AllNExclusion Erdos634.Draft.AllN2
open Erdos634.Draft.NSQRA Erdos634.Draft.NSQRW Erdos634.Draft.NSQS1 Erdos634.Draft.NSQChk Erdos634.Draft.NSQLegs
open Erdos634.Draft.NSQMain

open Erdos634.Draft.R8ZF Erdos634.Draft.E60Irr
open Erdos634.Draft.NSQRWT

def CN'zETD (N : ℕ) : Prop :=
  NQChk N ∧ EllChk2 N ∧ LeafNSq N ∧ LeafHAr N ∧ LeafR N ∧ LeafEsqN N ∧ LeafF1p N ∧ LeafS2 N ∧ LeafS3 N ∧ LeafIso N ∧
    LeafR8z N ∧ Erdos634.Draft.ThmD.GammaChkD N ∧ S1Chk N ∧ RWChkT N ∧ S5pChk N

instance (N : ℕ) : Decidable (CN'zETD N) := by unfold CN'zETD; infer_instance

/-- **The non-squarefree all-N theorem with the refined S5 leaf and Theorem D' at the G leaf** . -/
theorem not_tile_of_conditionsNSQzETD (N : ℕ) (h : CN'zETD N)
    (D : CongruentDissection N) : False := by
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
    (rwStatement_nsqT N (rwFreeT_of_chk hRW)) (raStatement_nsqM N (s5pFree_of_chk hRA))
    (fun hS => Erdos634.Draft.NSQCaseA.gapA_of_ell_nsq hS hNQ' hns (harith_of_chk hHAr) hℓ hℓ7 hodd)
    (caseB_of_sumsq N (fun D μ τ hs => Row2.theoremS_perm_nsq D μ τ hs hNQ') hns)
    ?_ (Erdos634.Draft.ThmD.caseG_of_gammaChkD Erdos634.Draft.ThmD.thmDStatement_geo hG) ?_ ?_ ?_
    (gapR8_of_chk_z hF2c hF3c hF4c) D
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

/-- `CN'zET N → CN'zETD N`: the new G leaf only weakens the old one. -/
theorem cnzETD_of_cnzET {N : ℕ} (h : CN'zET N) : CN'zETD N := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, hG, a13, a14, a15⟩ := h
  exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11,
    fun M hM hM0 hdv h3 hp hp' => Or.inl (hG M hM hM0 hdv h3 hp hp'), a13, a14, a15⟩

end Erdos634.Draft.NSQM

#print axioms Erdos634.Draft.NSQM.not_tile_of_conditionsNSQzETD
#print axioms Erdos634.Draft.NSQM.cnzETD_of_cnzET
