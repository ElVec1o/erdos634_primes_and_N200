/-
Draft/N92.lean -- `N = 92` is NOT a tile count.

`92 = 4 · 23` is the least value the arithmetic chain left undecided (`SpectrumLe91`).  Four search-type leaves fail their
arithmetic check at `N = 92`; each has exactly one instance, discharged by a kernel-checked free-branch-point certificate:

| leaf  | instance                                          | certificate                                              |
|-------|---------------------------------------------------|----------------------------------------------------------|
| S1    | `(t,p,q) = (2,2,3)`: tile (6,5,9), target (54,54,92)        | `Refl.MS1N92.not_dissection` (31,709 nodes, `CheckN` nogoods) |
| S4    | `(S',e,f) = (2,3,4)`: tile (12,7,16), target (56,138,128)   | `Refl.MC92.not_dissection` (3,374 nodes)                 |
| S5    | `(t,e,f) = (2,11,12)`: tile (132,23,144), target (552,552,506) | `Refl.MS92.not_dissection` (5,519 nodes)              |
| γ=2α  | arithmetic (`M = 2`, `k = 11`) + `GLK.caseG_of_leafOnly`    | `caseG_92`                                               |

Composite-N result.  NOT prime-case work.  No sorry, no native_decide.
-/
import Erdos634.Draft.N566076
import Erdos634.Draft.S1Inst
import Erdos634.Refl.MC92Sound
import Erdos634.Refl.MS92Sound
import Erdos634.Refl.MS1N92Sound

open scoped Classical
set_option maxRecDepth 8000
set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000

namespace Erdos634.Draft.N92

open Erdos634.Geometry Erdos634.Draft.TheoremPConditional Erdos634.Draft.Chain15 Erdos634.Draft.ChainComposite
open Erdos634.Draft.CompositeGen2 Erdos634.Draft.CompositeArith Erdos634.Draft.CompositeS2Arith
open Erdos634.Draft.CompositeS1Arith Erdos634.Draft.CompositeIsoB Erdos634.Draft.CompositeFinal2
open Erdos634.Draft.CompositeFinal3 Erdos634.Draft.AllNExclusion Erdos634.Draft.AllN2
open Erdos634.Draft.NSQRA Erdos634.Draft.NSQRW Erdos634.Draft.NSQS1 Erdos634.Draft.NSQChk Erdos634.Draft.NSQLegs
open Erdos634.Draft.NSQMain Erdos634.Draft.NSQM Erdos634.CertNode Erdos634.CertCoord

open Erdos634.Draft.N566076 Erdos634.Draft.CompositeFinal4

/-- `N566076.not_tile_of_leaves` with the S1 leaf supplied as a theorem. -/
theorem not_tile_of_leaves_s1 (N : ℕ) (hNQ : NQChk N) (hEll : EllChk2 N) (hNSq : LeafNSq N) (hHAr : LeafHAr N)
    (hR : LeafR N) (gE60 : GapE60 N) (hF1 : LeafF1p N) (hS2 : LeafS2 N) (hS3 : LeafS3 N) (hIso : LeafIso N)
    (hR8 : LeafR8 N) (gS1 : S1Closed N)
    (gS4 : RWStatementNsq N) (gS5 : RAStatementNsq N) (gG : CaseGClosed N) (gE120 : GapE120 N)
    (D : CongruentDissection N) : False := by
  obtain ⟨hF2c, hF3c, hF4c⟩ := hR8
  have hNQ' : Erdos634.Geometry.NQ N := nq_of_chk hNQ
  have hN7 : 7 ≤ N := by
    obtain ⟨s, n, hs, -, hNs, h7, -⟩ := hNQ'
    have : 1 ≤ s ^ 2 := Nat.one_le_pow _ _ hs
    rw [hNs]; nlinarith
  have hN0 : 0 < N := by omega
  have hns : ¬ ∃ x y : ℕ, N = x ^ 2 + y ^ 2 := nsq_of_chk hNSq
  obtain ⟨ℓ, hℓ, hℓ7, hodd⟩ := ell_of_chk2 hEll
  refine chain_nsq N gS1
    (s2Closed_of_arith N (s2Arith_of_chk hN0 hS2))
    (s3Closed_of_isoQRef N (isoQRef_of_chk hN0 hS3))
    (isoH9b_of_chk hN0 hIso)
    gS4 gS5
    (fun hS => Erdos634.Draft.NSQCaseA.gapA_of_ell_nsq hS hNQ' hns (harith_of_chk hHAr) hℓ hℓ7 hodd)
    (caseB_of_sumsq N (fun D μ τ hs => Row2.theoremS_perm_nsq D μ τ hs hNQ') hns)
    ?_ gG gE60 gE120 ?_ (gapR8_of_chk hF2c hF3c hF4c) D
  · rcases hR with hodd2 | ⟨hev, hnh⟩
    · exact caseR_of_odd N hodd2
    · exact caseR_of_H1 N (Erdos634.Draft.H1k.h1Right N) (nhsq_of_chk hev hnh)
  · rcases hF1 with h4 | hf
    · exact gapF1_of_mod4_two N h4
    · exact gapF1_of_chkpar (by omega) hf



/-! ## the certificate instances -/

theorem TGT_C92 : dist (Refl.MC92.TGT.pts 0) (Refl.MC92.TGT.pts 1) = 56 ∧
    dist (Refl.MC92.TGT.pts 1) (Refl.MC92.TGT.pts 2) = 138 ∧ dist (Refl.MC92.TGT.pts 0) (Refl.MC92.TGT.pts 2) = 128 :=
  model_sides_rp Refl.MC92.hDn Refl.MC92.TGT_pos (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem TGT_S92 : dist (Refl.MS92.TGT.pts 0) (Refl.MS92.TGT.pts 1) = 552 ∧
    dist (Refl.MS92.TGT.pts 1) (Refl.MS92.TGT.pts 2) = 552 ∧ dist (Refl.MS92.TGT.pts 0) (Refl.MS92.TGT.pts 2) = 506 :=
  model_sides_rp Refl.MS92.hDn Refl.MS92.TGT_pos (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem TGT_S1N92 : dist (Refl.MS1N92.TGT.pts 0) (Refl.MS1N92.TGT.pts 1) = 54 ∧
    dist (Refl.MS1N92.TGT.pts 1) (Refl.MS1N92.TGT.pts 2) = 92 ∧
    dist (Refl.MS1N92.TGT.pts 0) (Refl.MS1N92.TGT.pts 2) = 54 :=
  model_sides_rp Refl.MS1N92.hDn Refl.MS1N92.TGT_pos (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

open Erdos634.Geometry.GapE120Dis in
/-- `s5inst_of_cert` for a certificate whose target is labelled (leg, leg, base) in the vertex order `01, 12, 02` -/
theorem s5inst_of_cert_llb (t e f : ℤ) (TGT MODEL : Erdos634.Geometry.Tri)
    (hT : dist (TGT.pts 0) (TGT.pts 1) = (t : ℝ) * f * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ∧
      dist (TGT.pts 1) (TGT.pts 2) = (t : ℝ) * f * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ∧
      dist (TGT.pts 0) (TGT.pts 2) = (t : ℝ) * e * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2))
    (hM : dist (MODEL.pts 0) (MODEL.pts 1) = (e : ℝ) * f ∧
      dist (MODEL.pts 1) (MODEL.pts 2) = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 ∧ dist (MODEL.pts 0) (MODEL.pts 2) = (f : ℝ) ^ 2)
    (hno : ∀ {N : ℕ} (D : CongruentDissection N), D.target.Congruent TGT → D.model.Congruent MODEL → False) :
    S5Inst t e f := by
  intro N D h0 h1 h2 ⟨σ, m0, m1, m2⟩
  obtain ⟨g1, g2, g3⟩ := hT
  obtain ⟨k1, k2, k3⟩ := hM
  have hTc : D.target.Congruent TGT := by
    set ρ : Equiv.Perm (Fin 3) := Equiv.swap (1 : Fin 3) 2 with hρ
    have r0 : ρ 0 = 0 := by simp [hρ, sw0]
    have r1 : ρ 1 = 2 := by simp [hρ, sw1]
    have r2 : ρ 2 = 1 := by simp [hρ, sw2]
    have e02 : dist (D.target.pts 0) (D.target.pts 2) = D.target.oppLen 1 := by rw [dist_comm]; rfl
    have e21 : dist (D.target.pts 2) (D.target.pts 1) = D.target.oppLen 0 := by rw [dist_comm]; rfl
    have e01 : dist (D.target.pts 0) (D.target.pts 1) = D.target.oppLen 2 := rfl
    have hc := Tri.congruent_of_dist (D.target.relabel ρ) TGT
      (by simp only [Tri.relabel_pts, Function.comp]; rw [r0, r1, g1, e02, h1])
      (by simp only [Tri.relabel_pts, Function.comp]; rw [r1, r2, g2, e21, h0])
      (by simp only [Tri.relabel_pts, Function.comp]; rw [r0, r2, g3, e01, h2])
    exact (D.target.congruent_relabel ρ).trans hc
  obtain ⟨s1, s2, s3⟩ := sides_of_perm D.model σ
  rw [m0] at s1; rw [m1] at s2; rw [m2] at s3
  have hMc : D.model.Congruent MODEL := by
    set τ : Equiv.Perm (Fin 3) := (finRotate 3).trans σ with hτ
    have h0' : τ 0 = σ 1 := by simp [hτ, fr0]
    have h1' : τ 1 = σ 2 := by simp [hτ, fr1]
    have h2' : τ 2 = σ 0 := by simp [hτ, fr2]
    have hc := Tri.congruent_of_dist (D.model.relabel τ) MODEL
      (by simp only [Tri.relabel_pts, Function.comp]; rw [h0', h1', s1, k1])
      (by simp only [Tri.relabel_pts, Function.comp]; rw [h1', h2', dist_comm, s2, k2])
      (by simp only [Tri.relabel_pts, Function.comp]; rw [h0', h2', dist_comm, s3, k3])
    exact (D.model.congruent_relabel τ).trans hc
  exact hno D hTc hMc

/-- S4 `(S',e,f) = (2,3,4)`: tile `(12,7,16)`, target `(56,138,128)`. -/
theorem s4inst_2_3_4 : S4Inst 2 3 4 :=
  s4inst_of_cert 2 3 4 Refl.MC92.TGT Refl.MC92.MODEL
    ⟨by rw [TGT_C92.1]; norm_num, by rw [TGT_C92.2.1]; norm_num, by rw [TGT_C92.2.2]; norm_num⟩
    ⟨by rw [Refl.MC92.MODEL_sides.1]; norm_num, by rw [Refl.MC92.MODEL_sides.2.1]; norm_num,
      by rw [Refl.MC92.MODEL_sides.2.2]; norm_num⟩
    (fun D hT hM => Refl.MC92.not_dissection D hT hM)

/-- S5 `(t,e,f) = (2,11,12)`: tile `(132,23,144)`, target `(552,552,506)`. -/
theorem s5inst_2_11_12 : S5Inst 2 11 12 :=
  s5inst_of_cert_llb 2 11 12 Refl.MS92.TGT Refl.MS92.MODEL
    ⟨by rw [TGT_S92.1]; norm_num, by rw [TGT_S92.2.1]; norm_num, by rw [TGT_S92.2.2]; norm_num⟩
    ⟨by rw [Refl.MS92.MODEL_sides.1]; norm_num, by rw [Refl.MS92.MODEL_sides.2.1]; norm_num,
      by rw [Refl.MS92.MODEL_sides.2.2]; norm_num⟩
    (fun D hT hM => Refl.MS92.not_dissection D hT hM)

/-- S1 `(t,p,q) = (2,2,3)`: tile `(6,5,9)`, target legs `54`, base `92`. -/
theorem s1inst_2_2_3 : S1Inst 2 2 3 :=
  s1inst_of_cert_lbl 2 2 3 Refl.MS1N92.TGT Refl.MS1N92.MODEL
    ⟨by rw [TGT_S1N92.1]; norm_num, by rw [TGT_S1N92.2.1]; norm_num, by rw [TGT_S1N92.2.2]; norm_num⟩
    ⟨by rw [Refl.MS1N92.MODEL_sides.1]; norm_num, by rw [Refl.MS1N92.MODEL_sides.2.1]; norm_num,
      by rw [Refl.MS1N92.MODEL_sides.2.2]; norm_num⟩
    (fun D hT hM => Refl.MS1N92.not_dissection D hT hM)

/-! ## the leaves -/

/-- **`RWStatementNsq 92`** (S4): the scaled instance `(2,3,4)`. -/
theorem rw92 : RWStatementNsq 92 := by
  refine rwStatement_of_inst 92 ?_
  intro S' e f hS he hef hcop hN
  push_cast at hN
  have hd : f ^ 2 + 2 * f - 1 ≤ 2 * f ^ 2 - e ^ 2 := by nlinarith
  have hS4 : 4 ≤ S' ^ 2 := by nlinarith
  have hf2 : 2 ≤ f := by omega
  have hf : f ≤ 4 := by nlinarith
  have hS5 : S' ≤ 3 := by
    by_contra h; push_neg at h
    have : 16 ≤ S' ^ 2 := by nlinarith
    nlinarith
  interval_cases S' <;> interval_cases f <;> interval_cases e <;>
    first | (norm_num at hN; done) | exact @s4inst_2_3_4

/-- **`RAStatementNsq 92`** (S5): the scaled instance `(2,11,12)`. -/
theorem ra92 : RAStatementNsq 92 := by
  refine raStatement_of_inst 92 ?_
  intro t e f ht he hef hcop hN
  push_cast at hN
  have hd : 2 * f - 1 ≤ f ^ 2 - e ^ 2 := by nlinarith
  have ht4 : 4 ≤ t ^ 2 := by nlinarith
  have hf : f ≤ 12 := by nlinarith
  have ht5 : t ≤ 5 := by
    by_contra h; push_neg at h
    have : 36 ≤ t ^ 2 := by nlinarith
    nlinarith
  have hf2 : 2 ≤ f := by omega
  interval_cases t <;> interval_cases f <;> interval_cases e <;>
    first | (norm_num at hN; done) | exact @s5inst_2_11_12

/-- **`S1Closed 92`**: the scaled instance `(2,2,3)`. -/
theorem s1Closed_92 : S1Closed 92 := by
  refine s1Closed_of_inst 92 ?_
  intro t p q ht hp hpq hcop hN
  push_cast at hN
  have hd : 2 * q ^ 2 + 2 * q - 1 ≤ 3 * q ^ 2 - p ^ 2 := by nlinarith
  have ht4 : 4 ≤ t ^ 2 := by nlinarith
  have hq2 : 2 ≤ q := by omega
  have hq : q ≤ 3 := by nlinarith
  have ht5 : t ≤ 3 := by
    by_contra h; push_neg at h
    have : 16 ≤ t ^ 2 := by nlinarith
    nlinarith
  interval_cases t <;> interval_cases q <;> interval_cases p <;>
    first | (norm_num at hN; done) | exact @s1inst_2_2_3

theorem arith_92 : ∀ M M' : ℤ, 0 < M → 0 < M' → ((92 : ℕ) : ℤ) = M * M' → (2 : ℤ) ∣ M - ((92 : ℕ) : ℤ) →
    (2 : ℤ) ∣ M' - ((92 : ℕ) : ℤ) → 3 * M < M' → M = 2 ∧ M' = 2 * (2 * ((11 : ℕ) : ℤ) + 1) := by
  intro M M' hM hM' hN h1 h2 h3
  push_cast at *
  have : M ≤ 5 := by nlinarith
  interval_cases M <;> omega

/-- `CaseGClosed 92` (`γ = 2α`): `M = 2` is forced, and the leaf is `GLK.caseG_of_leafOnly`. -/
theorem caseG_92 : CaseGClosed 92 := Erdos634.GLK.caseG_of_leafOnly 92 11 (by norm_num) arith_92

/-- **`92` is not a tile count** (no `CongruentDissection 92` exists). -/
theorem not_tile_92 (D : CongruentDissection 92) : False :=
  not_tile_of_leaves_s1 92 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (gapE60_of_chk' (by norm_num) (by decide +kernel)) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    s1Closed_92 rw92 ra92 caseG_92 (gapE120_of_chk (by norm_num) (by decide +kernel)) D

end Erdos634.Draft.N92

#print axioms Erdos634.Draft.N92.not_tile_92
