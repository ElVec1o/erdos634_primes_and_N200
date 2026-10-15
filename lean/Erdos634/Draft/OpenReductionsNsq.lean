/-
Draft/OpenReductionsNsq.lean -- the open values `132`, `156`, `184` reduced to named instances.

`132 = 4 · 33` is not decided here.  Every leaf of the non-squarefree chain is closed in Lean except the isosceles
`2π/3` instance, carried as a hypothesis:

    theorem not_tile_132_of (h : IsoInst 5 3 7 6) (D : CongruentDissection 132) : False

(the tile `(5, 3, 7)` on the isosceles triangle with legs `42` and base `66`).  Closed leaves that need more than
arithmetic: `γ = 2α` (`GPairs132.caseG132`, certificate `Refl.MG132`), the `π/3` equilateral leaf
(`E60Apps.gapE60_132`), and S5, whose instances are `(2, 16, 17)` (dead by the two-`c`-edges filter) and `(2, 4, 7)`
(certificate `Refl.MS132`, used here for the first time).

Composite-N work; not prime-case work.  No sorry, no native_decide.
-/
import Erdos634.Draft.OpenReductions
import Erdos634.Draft.E60Reduce
import Erdos634.Draft.E60Apps
import Erdos634.Draft.GPairs132
import Erdos634.Draft.RATrap2
import Erdos634.Draft.RAInst
import Erdos634.Draft.E120Irr
import Erdos634.Refl.MS132Sound
import Erdos634.Draft.GPairArith
import Erdos634.Draft.S1Inst
import Erdos634.Draft.RWInst

open scoped Classical
set_option maxRecDepth 8000
set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000

namespace Erdos634.Draft.OpenRed

open Erdos634.Geometry Erdos634.Draft.TheoremPConditional Erdos634.Draft.Chain15 Erdos634.Draft.ChainComposite
open Erdos634.Draft.CompositeGen2 Erdos634.Draft.CompositeArith Erdos634.Draft.CompositeS2Arith
open Erdos634.Draft.CompositeS1Arith Erdos634.Draft.CompositeIsoB Erdos634.Draft.CompositeFinal2
open Erdos634.Draft.CompositeFinal3 Erdos634.Draft.AllNExclusion Erdos634.Draft.AllN2
open Erdos634.Draft.NSQRA Erdos634.Draft.NSQRW Erdos634.Draft.NSQS1 Erdos634.Draft.NSQChk Erdos634.Draft.NSQLegs
open Erdos634.Draft.NSQMain Erdos634.Draft.NSQM Erdos634.CertNode Erdos634.CertCoord
open Erdos634.Draft.N566076 Erdos634.Draft.CompositeFinal4 Erdos634.Draft.FDBBaseBetaE1
open Erdos634.Draft.IsoInst Erdos634.Draft.ChainIso Erdos634.Draft.R8ZF Erdos634.Draft.E60Reduce
open Erdos634.Draft.E120Irr Erdos634.Draft.AllN3 Erdos634.Draft.GPairCert Erdos634.Draft.GPairArith

/-! ## `N = 132` -/

theorem TGT_S132 : dist (Refl.MS132.TGT.pts 0) (Refl.MS132.TGT.pts 1) = 264 ∧
    dist (Refl.MS132.TGT.pts 1) (Refl.MS132.TGT.pts 2) = 462 ∧ dist (Refl.MS132.TGT.pts 0) (Refl.MS132.TGT.pts 2) = 462 :=
  model_sides_rp Refl.MS132.hDn Refl.MS132.TGT_pos (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

/-- S5 `(t,e,f) = (2,4,7)`: tile `(28,33,49)`, target `(462,462,264)`. -/
theorem s5inst_2_4_7 : S5Inst 2 4 7 :=
  s5inst_of_cert 2 4 7 Refl.MS132.TGT Refl.MS132.MODEL
    ⟨by rw [TGT_S132.1]; norm_num, by rw [TGT_S132.2.1]; norm_num, by rw [TGT_S132.2.2]; norm_num⟩
    ⟨by rw [Refl.MS132.MODEL_sides.1]; norm_num, by rw [Refl.MS132.MODEL_sides.2.1]; norm_num,
      by rw [Refl.MS132.MODEL_sides.2.2]; norm_num⟩
    (fun D hT hM => Refl.MS132.not_dissection D hT hM)

/-- **`RAStatementNsq 132`** (S5): `(2,16,17)` by the two-`c`-edges filter, `(2,4,7)` by certificate. -/
theorem ra132 : RAStatementNsq 132 := by
  refine raStatement_of_inst_trap2 132 ?_
  intro t e f ht he hef hcop hN hwb _
  push_cast at hN
  have hd : 2 * f - 1 ≤ f ^ 2 - e ^ 2 := by nlinarith
  have ht4 : 4 ≤ t ^ 2 := by nlinarith
  have hf : f ≤ 17 := by nlinarith
  have ht5 : t ≤ 6 := by
    by_contra h; push_neg at h
    have : 49 ≤ t ^ 2 := by nlinarith
    nlinarith
  have hf2 : 2 ≤ f := by omega
  have hk : ¬ S5Word2 2 16 17 := s5word2_k (k := 16) (by norm_num)
  interval_cases t <;> interval_cases f <;> interval_cases e <;>
    first | (norm_num at hN; done) | (exfalso; exact hk hwb) | exact @s5inst_2_4_7

/-- the isosceles leaf of `132` from its one instance -/
theorem iso_132_of (h : IsoInst 5 3 7 6) : IsoClosed 132 := by
  refine isoClosed_of_inst 132 (isoInstHyp_of_chkL (by norm_num) [(5, 3)] (by decide +kernel) ?_)
  intro p hp c₀ k hc hk hcc harea
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  subst hp
  dsimp only at hcc harea ⊢
  push_cast at hcc harea
  have hc2 : c₀ ^ 2 = 49 := by linarith
  have hk2 : k ^ 2 = 36 := by linarith
  have e1 : c₀ = 7 := by
    have h7 : (c₀ - 7) * (c₀ + 7) = 0 := by linear_combination hc2
    rcases mul_eq_zero.mp h7 with h' | h' <;> omega
  have e2 : k = 6 := by
    have h6 : (k - 6) * (k + 6) = 0 := by linear_combination hk2
    rcases mul_eq_zero.mp h6 with h' | h' <;> omega
  subst e1 e2
  first
    | exact @h
    | (intro N' D' hT hM
       exact h D' (by simpa using hT) (by simpa using hM))

/-- the list is sharp -/
theorem iso_132_sharp : ¬ IsoChkL 132 [] := by decide +kernel

/-- **`132` is not a tile count, given its one remaining instance**: the tile `(5, 3, 7)` on the isosceles
triangle with legs `42` and base `66`. -/
theorem not_tile_132_of (h : IsoInst 5 3 7 6) (D : CongruentDissection 132) : False :=
  not_tile_nsq_full 132 (by decide +kernel) (by decide +kernel) (leafNSq_of_sq (by decide +kernel))
    (leafHAr_of_sq (by decide +kernel)) (by decide +kernel) (leafS2_of_sq (by decide +kernel))
    (s1Closed_of_free 132 (s1Free_of_chk (by decide +kernel)))
    (s3Closed_of_isoQRef 132 (isoQRef_of_chk (by norm_num) (s3Chk_of_sq (by decide +kernel))))
    (iso_132_of h)
    (rwStatement_nsq 132 (rwFree_of_chk (by decide +kernel)))
    ra132 Erdos634.Draft.GPairs132.caseG132 Erdos634.Draft.E60Apps.gapE60_132
    (gapE120_of_chk_sq [] (by decide +kernel) (by intro p hp; cases hp))
    (gapF1_of_leaf (by norm_num) (by decide +kernel))
    (gapR8_of_chk_z (noF2Chk_of_sq (by decide +kernel)) (noF3zChk_of_sq (by decide +kernel))
      (noF4zChk_of_sq (by decide +kernel))) D

/-! ## `N = 184` -/

/-- the S4 leaf of `184` from its one instance: tile `(10, 21, 25)`, target `(184, 210, 250)` -/
theorem rw184_of (h : S4Inst 2 2 5) : RWStatementNsq 184 := by
  refine rwStatement_of_inst 184 ?_
  intro S' e f hS he hef hcop hN
  push_cast at hN
  have hd : f ^ 2 + 2 * f - 1 ≤ 2 * f ^ 2 - e ^ 2 := by nlinarith
  have hS4 : 4 ≤ S' ^ 2 := by nlinarith
  have hf2 : 2 ≤ f := by omega
  have hf : f ≤ 6 := by nlinarith
  have hS5 : S' ≤ 5 := by
    by_contra h'; push_neg at h'
    have : 36 ≤ S' ^ 2 := by nlinarith
    nlinarith
  interval_cases S' <;> interval_cases f <;> interval_cases e <;>
    first | (norm_num at hN; done) | exact @h

/-- the isosceles leaf of `184` from its one instance: tile `(7, 8, 13)`, target legs `104`, base `184` -/
theorem iso_184_of (h : IsoInst 7 8 13 8) : IsoClosed 184 := by
  refine isoClosed_of_inst 184 (isoInstHyp_of_chkL (by norm_num) [(7, 8)] (by decide +kernel) ?_)
  intro p hp c₀ k hc hk hcc harea
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  subst hp
  dsimp only at hcc harea ⊢
  push_cast at hcc harea
  have hc2 : c₀ ^ 2 = 169 := by linarith
  have hk2 : k ^ 2 = 64 := by linarith
  have e1 : c₀ = 13 := by
    have h13 : (c₀ - 13) * (c₀ + 13) = 0 := by linear_combination hc2
    rcases mul_eq_zero.mp h13 with h' | h' <;> omega
  have e2 : k = 8 := by
    have h8 : (k - 8) * (k + 8) = 0 := by linear_combination hk2
    rcases mul_eq_zero.mp h8 with h' | h' <;> omega
  subst e1 e2
  first
    | exact @h
    | (intro N' D' hT hM
       exact h D' (by simpa using hT) (by simpa using hM))

/-- **`184` is not a tile count, given its two remaining instances.** -/
theorem not_tile_184_of (h1 : IsoInst 7 8 13 8) (h2 : S4Inst 2 2 5) (D : CongruentDissection 184) : False :=
  not_tile_nsq_full 184 (by decide +kernel) (by decide +kernel) (leafNSq_of_sq (by decide +kernel))
    (leafHAr_of_sq (by decide +kernel)) (by decide +kernel) (leafS2_of_sq (by decide +kernel))
    (s1Closed_of_free 184 (s1Free_of_chk (by decide +kernel)))
    (s3Closed_of_isoQRef 184 (isoQRef_of_chk (by norm_num) (s3Chk_of_sq (by decide +kernel))))
    (iso_184_of h1) (rw184_of h2)
    (raStatement_nsqM 184 (s5pFree_of_chk (by decide +kernel)))
    (caseG_of_gammaArith 184 (gammaArith_of_chk (by decide +kernel)))
    (Erdos634.Draft.E60Irr.gapE60_of_chk_sq (by norm_num) [] (by decide +kernel) (by intro p hp; cases hp))
    (gapE120_of_chk_sq [] (by decide +kernel) (by intro p hp; cases hp))
    (gapF1_of_leaf (by norm_num) (by decide +kernel))
    (gapR8_of_chk_z (noF2Chk_of_sq (by decide +kernel)) (noF3zChk_of_sq (by decide +kernel))
      (noF4zChk_of_sq (by decide +kernel))) D

/-! ## `N = 156` -/

/-- the S1 leaf of `156` from its one instance: the member `(3, 4)` at scale `2`, tile `(12, 7, 16)`, target legs
`128`, base `234` -/
theorem s1_156_of (h : S1Inst 2 3 4) : S1Closed 156 := by
  refine s1Closed_of_inst 156 ?_
  intro t p q ht hp hpq hcop hN
  push_cast at hN
  have hd : 2 * q ^ 2 + 2 * q - 1 ≤ 3 * q ^ 2 - p ^ 2 := by nlinarith
  have ht4 : 4 ≤ t ^ 2 := by nlinarith
  have hq2 : 2 ≤ q := by omega
  have hq : q ≤ 4 := by nlinarith
  have ht5 : t ≤ 4 := by
    by_contra h'; push_neg at h'
    have : 25 ≤ t ^ 2 := by nlinarith
    nlinarith
  interval_cases t <;> interval_cases q <;> interval_cases p <;>
    first | (norm_num at hN; done) | exact @h

/-- the S5 leaf of `156`: `(2, 19, 20)` by the two-`c`-edges filter, `(2, 5, 8)` carried as an instance (tile
`(40, 39, 64)`) -/
theorem ra156_of (h : S5Inst 2 5 8) : RAStatementNsq 156 := by
  refine raStatement_of_inst_trap2 156 ?_
  intro t e f ht he hef hcop hN hwb _
  push_cast at hN
  have hd : 2 * f - 1 ≤ f ^ 2 - e ^ 2 := by nlinarith
  have ht4 : 4 ≤ t ^ 2 := by nlinarith
  have hf : f ≤ 20 := by nlinarith
  have ht5 : t ≤ 7 := by
    by_contra h'; push_neg at h'
    have : 64 ≤ t ^ 2 := by nlinarith
    nlinarith
  have hf2 : 2 ≤ f := by omega
  have hk : ¬ S5Word2 2 19 20 := s5word2_k (k := 19) (by norm_num)
  interval_cases t <;> interval_cases f <;> interval_cases e <;>
    first | (norm_num at hN; done) | (exfalso; exact hk hwb) | exact @h

/-- the `γ = 2α` leaf of `156`: `(2, 78)` by Lemma G*, `(6, 26)` carried as a pair (tile `(25, 39, 40)`, target
legs `390`, base `624`) -/
theorem caseG156_of (h : GPair 156 6 26) : CaseGClosed 156 := by
  refine caseG_of_pairs 156 [(2, 78), (6, 26)] ?_ ?_
  · intro M M' hM hM' hN h1 h2 h3
    push_cast at hN h1 h2
    have hM7 : M ≤ 7 := by nlinarith
    have key : (M = 2 ∧ M' = 78) ∨ (M = 6 ∧ M' = 26) := by
      interval_cases M <;> omega
    rcases key with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · have h' := gPair_of_leafG 156 19 (by norm_num)
      norm_num at h'
      exact h'
    · exact h

/-- **`156` is not a tile count, given its three remaining instances.**  (`GPair 156 6 26` and `S5Inst 2 5 8` have
certificates that are generated and not kernel-checked at the time of writing: `Refl.MG156`, `Refl.MS156`.) -/
theorem not_tile_156_of (h1 : S1Inst 2 3 4) (h2 : S5Inst 2 5 8) (h3 : GPair 156 6 26)
    (D : CongruentDissection 156) : False :=
  not_tile_nsq_full 156 (by decide +kernel) (by decide +kernel) (leafNSq_of_sq (by decide +kernel))
    (leafHAr_of_sq (by decide +kernel)) (by decide +kernel) (leafS2_of_sq (by decide +kernel))
    (s1_156_of h1)
    (s3Closed_of_isoQRef 156 (isoQRef_of_chk (by norm_num) (s3Chk_of_sq (by decide +kernel))))
    (isoClosed_of_chk (by norm_num) (by decide +kernel))
    (rwStatement_nsq 156 (rwFree_of_chk (by decide +kernel)))
    (ra156_of h2) (caseG156_of h3) Erdos634.Draft.E60Apps.gapE60_156
    (gapE120_of_chk_sq [] (by decide +kernel) (by intro p hp; cases hp))
    (gapF1_of_leaf (by norm_num) (by decide +kernel))
    (gapR8_of_chk_z (noF2Chk_of_sq (by decide +kernel)) (noF3zChk_of_sq (by decide +kernel))
      (noF4zChk_of_sq (by decide +kernel))) D

end Erdos634.Draft.OpenRed

#print axioms Erdos634.Draft.OpenRed.not_tile_132_of
#print axioms Erdos634.Draft.OpenRed.not_tile_184_of
#print axioms Erdos634.Draft.OpenRed.not_tile_156_of
