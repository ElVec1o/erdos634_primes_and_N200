/-
Draft/N204N228.lean -- `N = 204` and `N = 228` are NOT tile counts.

`204 = 4 * 3 * 17`, `228 = 4 * 3 * 19`.  Every leaf of `CN'zET` holds by kernel-checked arithmetic except the `gamma = 2 alpha`
leaf `GammaChk` (the pair `(6, 34)` of `204` and `(6, 38)` of `228`, both `g = 2`, `(u, v) = (7, 10)` and `(8, 11)`).  The pair
`(2, 2(2k+1))` is closed by `GPairCert.gPair_of_leafG`; the pair `(6, M')` by the certificates `Refl.MG204` (tile `(49, 51, 70)`,
legs `714`, base `1020`) and `Refl.MG228` (tile `(64, 57, 88)`, legs `912`, base `1254`), exactly as `N171`.
Composite-N result.  No sorry, no native_decide.
-/
import Erdos634.Draft.NSQMain
import Erdos634.Draft.NSQMRA
import Erdos634.Draft.R8ZFLeaf
import Erdos634.Draft.NSQMMainZ
import Erdos634.Draft.E60Irr
import Erdos634.Draft.NSQRWT

import Erdos634.Draft.NSQMMainZET
import Erdos634.Draft.NSQMMainZETW
import Erdos634.Draft.HasSidesPerm
import Erdos634.Draft.FDBBaseBetaE1
import Erdos634.Draft.TileCountFamilies
import Erdos634.Draft.GPairCert
import Erdos634.Draft.E60Reduce
import Erdos634.Draft.RAInst
import Erdos634.Draft.GPairArith
import Erdos634.Refl.MG204Sound
import Erdos634.Refl.MG228Sound

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

open Erdos634.Draft.GPairCert Erdos634.Draft.GPairArith Erdos634.CertNode Erdos634.CertCoord
open Erdos634.Draft.FDBBaseBetaE1 Erdos634.Draft.TileCountFamilies

/-- `CN'zET` without its `GammaChk` conjunct -/
def CNzETnoG (N : ℕ) : Prop :=
  NQChk N ∧ EllChk2 N ∧ LeafNSq N ∧ LeafHAr N ∧ LeafR N ∧ LeafEsqN N ∧ LeafF1p N ∧ LeafS2 N ∧ LeafS3 N ∧ LeafIso N ∧
    LeafR8z N ∧ S1Chk N ∧ RWChkT N ∧ S5wChk N

instance (N : ℕ) : Decidable (CNzETnoG N) := by unfold CNzETnoG; infer_instance

/-- `not_tile_of_conditionsNSQzET` with the `gamma = 2 alpha` leaf supplied as `CaseGClosed N` -/
theorem not_tile_of_conditionsNSQzET_noG (N : ℕ) (h : CNzETnoG N) (gG : CaseGClosed N) (D : CongruentDissection N) : False := by
  obtain ⟨hNQ, hEll, hNSq, hHAr, hR, hE, hF1, hS2, hS3, hIso, ⟨hF2c, hF3c, hF4c⟩, hS1, hRW, hRA⟩ := h
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
    (rwStatement_nsqT N (rwFreeT_of_chk hRW)) (raStatement_of_s5w N hRA)
    (fun hS => Erdos634.Draft.NSQCaseA.gapA_of_ell_nsq hS hNQ' hns (harith_of_chk hHAr) hℓ hℓ7 hodd)
    (caseB_of_sumsq N (fun D μ τ hs => Row2.theoremS_perm_nsq D μ τ hs hNQ') hns)
    ?_ gG ?_ ?_ ?_ (gapR8_of_chk_z hF2c hF3c hF4c) D
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


theorem TGT_G204 : dist (Refl.MG204.TGT.pts 0) (Refl.MG204.TGT.pts 1) = 714 ∧
    dist (Refl.MG204.TGT.pts 1) (Refl.MG204.TGT.pts 2) = 714 ∧ dist (Refl.MG204.TGT.pts 0) (Refl.MG204.TGT.pts 2) = 1020 :=
  model_sides_rp Refl.MG204.hDn Refl.MG204.TGT_pos (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

/-- the pair `(M, M') = (6, 34)` of `204`: tile `(49, 51, 70)`, legs `714`, base `1020` -/
theorem gpair_204_6_34 : GPair 204 6 34 := by
  obtain ⟨g1, g2, g3⟩ := TGT_G204
  obtain ⟨k1, k2, k3⟩ := Refl.MG204.MODEL_sides
  exact gPair_of_cert 204 6 34 (by norm_num) 714 1020 49 51 70 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) Refl.MG204.TGT Refl.MG204.MODEL
    (fun T h => congruent_of_hasSides' (hasSides_rot h) g1 g2 g3)
    (fun T h => congruent_of_hasSides' (hasSides_rot h) k1 k2 k3)
    (fun D' hT hM => Refl.MG204.not_dissection D' hT hM)

theorem caseG204 : CaseGClosed 204 := by
  refine caseG_of_pairs 204 [(2, 102), (6, 34)] ?_ ?_
  · intro M M' hM hM' hN h1 h2 h3
    push_cast at hN h1 h2
    have hM7 : M ≤ 8 := by nlinarith
    have key : (M = 2 ∧ M' = 102) ∨ (M = 6 ∧ M' = 34) := by
      interval_cases M <;> omega
    rcases key with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact gPair_of_leafG 204 25 (by norm_num)
    · exact gpair_204_6_34

theorem not_tile_204 (D : CongruentDissection 204) : False :=
  not_tile_of_conditionsNSQzET_noG 204 (by decide +kernel) caseG204 D

theorem TGT_G228 : dist (Refl.MG228.TGT.pts 0) (Refl.MG228.TGT.pts 1) = 912 ∧
    dist (Refl.MG228.TGT.pts 1) (Refl.MG228.TGT.pts 2) = 912 ∧ dist (Refl.MG228.TGT.pts 0) (Refl.MG228.TGT.pts 2) = 1254 :=
  model_sides_rp Refl.MG228.hDn Refl.MG228.TGT_pos (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

/-- the pair `(M, M') = (6, 38)` of `228`: tile `(64, 57, 88)`, legs `912`, base `1254` -/
theorem gpair_228_6_38 : GPair 228 6 38 := by
  obtain ⟨g1, g2, g3⟩ := TGT_G228
  obtain ⟨k1, k2, k3⟩ := Refl.MG228.MODEL_sides
  exact gPair_of_cert 228 6 38 (by norm_num) 912 1254 64 57 88 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) Refl.MG228.TGT Refl.MG228.MODEL
    (fun T h => congruent_of_hasSides' (hasSides_rot h) g1 g2 g3)
    (fun T h => congruent_of_hasSides' (hasSides_rot h) k1 k2 k3)
    (fun D' hT hM => Refl.MG228.not_dissection D' hT hM)

theorem caseG228 : CaseGClosed 228 := by
  refine caseG_of_pairs 228 [(2, 114), (6, 38)] ?_ ?_
  · intro M M' hM hM' hN h1 h2 h3
    push_cast at hN h1 h2
    have hM7 : M ≤ 8 := by nlinarith
    have key : (M = 2 ∧ M' = 114) ∨ (M = 6 ∧ M' = 38) := by
      interval_cases M <;> omega
    rcases key with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact gPair_of_leafG 228 28 (by norm_num)
    · exact gpair_228_6_38

theorem not_tile_228 (D : CongruentDissection 228) : False :=
  not_tile_of_conditionsNSQzET_noG 228 (by decide +kernel) caseG228 D

theorem not_tileCount_204 : ¬ TileCount 204 := fun ⟨D⟩ => not_tile_204 D
theorem not_tileCount_228 : ¬ TileCount 228 := fun ⟨D⟩ => not_tile_228 D

end Erdos634.Draft.NSQM

#print axioms Erdos634.Draft.NSQM.not_tile_204
#print axioms Erdos634.Draft.NSQM.not_tile_228
