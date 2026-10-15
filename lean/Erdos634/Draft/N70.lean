/-
Draft/N70.lean -- `70` is not a tile count.

`70` is squarefree and satisfies every leaf of `AllN2.C'` except S3 (`C' 70` is false).
Its S3 leaf is the single base-α instance `(e, d, m) = (2, 1, 1)`: tile `(6,5,9)`, isosceles target `(45,45,70)`,
refuted by the kernel-checked free-branch-point certificate `Refl.MB70.not_dissection` (19,953 nodes).

Composite-N result.  No sorry, no native_decide.
-/
import Erdos634.Draft.S3Inst
import Erdos634.Refl.MB70Sound
import Erdos634.Draft.AllN2Cond

open scoped Classical
set_option maxRecDepth 8000
set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000

namespace Erdos634.Draft.AllN2

open Erdos634.Geometry Erdos634.Draft.TheoremPConditional Erdos634.Draft.Chain15 Erdos634.Draft.ChainComposite
open Erdos634.Draft.CompositeGen2 Erdos634.Draft.CompositeArith Erdos634.Draft.CompositeS2Arith
open Erdos634.Draft.CompositeS1Arith Erdos634.Draft.CompositeIsoB Erdos634.Draft.CompositeFinal2
open Erdos634.Draft.CompositeFinal3 Erdos634.Draft.AllNExclusion
open Erdos634.CertNode Erdos634.CertCoord

/-- `not_tile_of_conditions'` with the S3 leaf supplied as a theorem. -/
theorem not_tile_of_leaves_sqf (N : ℕ) (hsq : LeafSqf N) (hrange : LeafRange N) (hEll : LeafEll N) (hNSq : LeafNSq N)
    (hHAr : LeafHAr N) (hR : LeafR N) (hE : LeafE' N) (hF1 : LeafF1 N) (hS2 : LeafS2 N)
    (gS3 : S3Closed N) (hIso : LeafIso N) (hR8 : LeafR8 N) (D : CongruentDissection N) : False := by
  obtain ⟨h7, h17⟩ := hrange
  obtain ⟨hF2c, hF3c, hF4c⟩ := hR8
  have hN0 : 0 < N := by omega
  have hns : ¬ ∃ x y : ℕ, N = x ^ 2 + y ^ 2 := nsq_of_chk hNSq
  obtain ⟨ℓ, hℓ, hℓ7, hodd⟩ := ell_of_chk hsq hEll
  refine chain_gen3 N hsq (s1Closed_of_sqfree N hsq hN0)
    (s2Closed_of_arith N (s2Arith_of_chk hN0 hS2))
    gS3
    (isoH9b_of_chk hN0 hIso)
    (fun hS => Erdos634.CaseA.RCompositeE.gapA_of_ellE hS hsq h7 h17 hns (harith_of_chk hHAr) hℓ hℓ7 hodd)
    (caseB_of_sumsq N (fun D μ τ hs => Row2.theoremS_perm_sqfreeE D μ τ hs hsq h7 h17) hns)
    ?_ (Erdos634.Draft.CompositeFinal10.caseG_of_squarefree N hsq) ?_ ?_ ?_ (gapR8_of_chk hF2c hF3c hF4c) D
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
    · exact gapF1_of_chk (by omega) hf

theorem TGT_B70 : dist (Refl.MB70.TGT.pts 0) (Refl.MB70.TGT.pts 1) = 70 ∧
    dist (Refl.MB70.TGT.pts 1) (Refl.MB70.TGT.pts 2) = 45 ∧ dist (Refl.MB70.TGT.pts 0) (Refl.MB70.TGT.pts 2) = 45 :=
  model_sides_rp Refl.MB70.hDn Refl.MB70.TGT_pos (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

/-- S3 `(m,e,f) = (1,2,3)`: tile `(6,5,9)`, isosceles target `(45,45,70)`. -/
theorem s3inst_1_2_3 : S3Inst 1 2 3 :=
  s3inst_of_cert 1 2 3 Refl.MB70.TGT Refl.MB70.MODEL
    ⟨by rw [TGT_B70.1]; norm_num, by rw [TGT_B70.2.1]; norm_num, by rw [TGT_B70.2.2]; norm_num⟩
    ⟨by rw [Refl.MB70.MODEL_sides.1]; norm_num, by rw [Refl.MB70.MODEL_sides.2.1]; norm_num,
      by rw [Refl.MB70.MODEL_sides.2.2]; norm_num⟩
    (fun D hT hM => Refl.MB70.not_dissection D hT hM)

/-- **`S3Closed 70`**: the reduced Row-11 equation at `N = 70` has the single solution `(e,d,m) = (2,1,1)`. -/
theorem s3Closed_70 : S3Closed 70 := by
  refine s3Closed_of_inst 70 ?_
  intro e d m he hd hcop heq
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h; simp at heq; omega
    · exact h
  have hm2 : 1 ≤ m ^ 2 := Nat.one_le_pow _ _ hm1
  have hX : (2 * e + d) * (e ^ 2 + 4 * e * d + 2 * d ^ 2) ≤ 70 * d := by
    rw [heq]; exact Nat.le_mul_of_pos_left _ hm2
  have hQ : e ^ 2 + 4 * e * d + 2 * d ^ 2 ≤ 70 := by
    by_contra h
    push_neg at h
    have : 70 * d < (2 * e + d) * (e ^ 2 + 4 * e * d + 2 * d ^ 2) := by nlinarith
    omega
  have he8 : e ≤ 8 := by nlinarith
  have hd5 : d ≤ 5 := by nlinarith
  have hm8 : m ≤ 8 := by
    by_contra h
    push_neg at h
    have h81 : 81 ≤ m ^ 2 := by nlinarith
    have h21 : 21 ≤ (2 * e + d) * (e ^ 2 + 4 * e * d + 2 * d ^ 2) := by nlinarith
    have : 81 * 21 ≤ m ^ 2 * ((2 * e + d) * (e ^ 2 + 4 * e * d + 2 * d ^ 2)) := Nat.mul_le_mul h81 h21
    omega
  interval_cases e <;> interval_cases d <;> interval_cases m <;>
    first | (norm_num at heq; done) | exact @s3inst_1_2_3

/-- **`70` is not a tile count** (no `CongruentDissection 70` exists). -/
theorem not_tile_70 (D : CongruentDissection 70) : False :=
  not_tile_of_leaves_sqf 70 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    s3Closed_70 (by decide +kernel) (by decide +kernel) D

end Erdos634.Draft.AllN2

#print axioms Erdos634.Draft.AllN2.not_tile_70
