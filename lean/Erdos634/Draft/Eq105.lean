/-
Draft/Eq105.lean: no equilateral triangle can be cut into 105 congruent triangles.

The dispatch chain of `ChainIso.chain_gen3_iso` is run on a dissection `D` of an equilateral target into 105 tiles:
* rational-angle tile, similar tile, right tile, `γ = 2α`, the five `3α + 2β = π` targets, and the `2π/3` tile on an
  equilateral / isosceles / `F₂–F₄` target: the arithmetic leaves of `N = 105` (all pass by `decide +kernel`);
* `2π/3` tile on an `F₁` target: impossible here because an `F₁` target has an angle `α` or `π/3 − α`, which for an
  equilateral target would make `α/π` rational (no `N`-level `F₁` leaf is used);
* tile with an angle `π/3` (`GapE60 105`): the pair table `E60Cert.Pairs60ChkExc 105 [(45,7), (35,9)]` and the two
  kernel-checked certificates `Refl.MQ105B` (tile (5,19,21), 7,841 nodes) and `Refl.MQ105A` (tile (7,13,15),
  14,517 nodes) for the equilateral triangle of side 105.

Two exhaustive searches (1,922,194 and 3,497,208 nodes, uncertified) are thereby replaced by certificates, and a third
(the `2π/3` tile (21,320,331), 25,742,338 nodes) is not needed: `Pairs120Chk 105` holds.

No sorry, no native_decide.
-/
import Erdos634.Draft.E60Cert
import Erdos634.Draft.ChainIso
import Erdos634.Draft.R8ZFLeaf
import Erdos634.Refl.MQ105ASound
import Erdos634.Refl.MQ105BSound

open scoped Classical
set_option maxRecDepth 8000
set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000

namespace Erdos634.Draft.Eq105

open Erdos634.Geometry Erdos634.Draft.TheoremPConditional Erdos634.Draft.Chain15 Erdos634.Draft.ChainComposite
open Erdos634.Draft.CompositeGen2 Erdos634.Draft.CompositeArith Erdos634.Draft.CompositeS2Arith
open Erdos634.Draft.CompositeS1Arith Erdos634.Draft.CompositeIsoB Erdos634.Draft.CompositeFinal2
open Erdos634.Draft.CompositeFinal3 Erdos634.Draft.AllNExclusion Erdos634.Draft.AllN2
open Erdos634.Draft.NSQRA Erdos634.Draft.NSQRW Erdos634.Draft.NSQS1 Erdos634.Draft.NSQChk Erdos634.Draft.NSQLegs
open Erdos634.Draft.NSQMain Erdos634.Draft.NSQM Erdos634.CertNode Erdos634.CertCoord
open Erdos634.Draft.N566076 Erdos634.Draft.CompositeFinal4 Erdos634.Draft.IsoInst Erdos634.Draft.ChainIso
open Erdos634.Draft.CompositeE5Gen Erdos634.Draft.E60Cert Erdos634.Draft.FDBBaseBetaE1 Erdos634.Draft.R8ZF

theorem TGT_A : dist (Refl.MQ105A.TGT.pts 0) (Refl.MQ105A.TGT.pts 1) = ((105 : ℕ) : ℝ) ∧
    dist (Refl.MQ105A.TGT.pts 1) (Refl.MQ105A.TGT.pts 2) = ((105 : ℕ) : ℝ) ∧
    dist (Refl.MQ105A.TGT.pts 0) (Refl.MQ105A.TGT.pts 2) = ((105 : ℕ) : ℝ) :=
  model_sides_rp Refl.MQ105A.hDn Refl.MQ105A.TGT_pos (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem TGT_B : dist (Refl.MQ105B.TGT.pts 0) (Refl.MQ105B.TGT.pts 1) = ((105 : ℕ) : ℝ) ∧
    dist (Refl.MQ105B.TGT.pts 1) (Refl.MQ105B.TGT.pts 2) = ((105 : ℕ) : ℝ) ∧
    dist (Refl.MQ105B.TGT.pts 0) (Refl.MQ105B.TGT.pts 2) = ((105 : ℕ) : ℝ) :=
  model_sides_rp Refl.MQ105B.hDn Refl.MQ105B.TGT_pos (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

/-- the pair `(35, 9)`: tile `(15, 7, 13)` (angle `π/3` between the sides 15 and 7), equilateral side 105 -/
theorem pair_35_9 : E60Pair 105 ((35 : ℕ) : ℤ) ((9 : ℕ) : ℤ) := by
  obtain ⟨k1, k2, k3⟩ := Refl.MQ105A.MODEL_sides
  exact e60Pair_of_cert 105 (by norm_num) _ _ (by norm_num) (by norm_num) (by norm_num) 15 7 13
    (by norm_num) (by norm_num) (by norm_num) Refl.MQ105A.TGT Refl.MQ105A.MODEL TGT_A
    (fun T h => congruent_of_hasSides' (hasSides_rot (hasSides_rot h)) k1 k2 k3)
    (fun D' hT hM => Refl.MQ105A.not_dissection D' hT hM)

/-- the pair `(45, 7)`: tile `(21, 5, 19)` (angle `π/3` between the sides 21 and 5), equilateral side 105 -/
theorem pair_45_7 : E60Pair 105 ((45 : ℕ) : ℤ) ((7 : ℕ) : ℤ) := by
  obtain ⟨k1, k2, k3⟩ := Refl.MQ105B.MODEL_sides
  exact e60Pair_of_cert 105 (by norm_num) _ _ (by norm_num) (by norm_num) (by norm_num) 21 5 19
    (by norm_num) (by norm_num) (by norm_num) Refl.MQ105B.TGT Refl.MQ105B.MODEL TGT_B
    (fun T h => congruent_of_hasSides' (hasSides_rot (hasSides_rot h)) k1 k2 k3)
    (fun D' hT hM => Refl.MQ105B.not_dissection D' hT hM)

/-- **`GapE60 105`**: no tile with an angle `π/3` (and an irrational angle) cuts an equilateral triangle into 105. -/
theorem gapE60_105 : GapE60 105 := by
  refine gapE60_of_chk_exc (by norm_num) [(45, 7), (35, 9)] (by decide +kernel) ?_
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact pair_45_7
  · exact pair_35_9

/-- an `F₁` target is not equilateral (`α/π` would be rational) -/
theorem f1_not_equilateral {N : ℕ} (D : CongruentDissection N) {α : ℝ} (hα : IrrPi α) (hf : F1Shape D α)
    (hE : Equilateral D) : False := by
  have hpi := Real.pi_pos
  rcases hf with ⟨τ, t0, -, -⟩ | ⟨τ, t0, -, -⟩
  · rw [hE (τ 0)] at t0
    exact hα ⟨1 / 3, by push_cast; linarith⟩
  · rw [hE (τ 0)] at t0
    exact hα ⟨0, by push_cast; linarith⟩

/-- **`thm:eq105`.**  No equilateral triangle can be cut into 105 congruent triangles. -/
theorem eq105 (D : CongruentDissection 105) (hE : Equilateral D) : False := by
  have hsq : Squarefree 105 := by decide +kernel
  have hN0 : 0 < 105 := by norm_num
  have hns : ¬ ∃ x y : ℕ, 105 = x ^ 2 + y ^ 2 := nsq_of_chk (by decide +kernel)
  obtain ⟨ℓ, hℓ, hℓ7, hodd⟩ := ell_of_chk hsq (show LeafEll 105 by decide +kernel)
  -- Case A
  by_cases hA : ∀ k, ∃ q : ℚ, D.model.angleAt k = q * Real.pi
  · exact Erdos634.CaseA.RCompositeE.gapA_of_ellE Erdos634.LemmaSAll.lemmaS hsq (by norm_num) (by norm_num) hns
      (harith_of_chk (show LeafHAr 105 by decide +kernel)) hℓ hℓ7 hodd D hA
  have hirr : ∃ k, IrrPi (D.model.angleAt k) := by
    by_contra hc
    exact hA fun k => by_contra fun hk => hc ⟨k, hk⟩
  -- Case B
  by_cases hB : SimilarTM D
  · obtain ⟨μ, τ, hs⟩ := hB
    exact caseB_of_sumsq 105 (fun D μ τ hs => Row2.theoremS_perm_sqfreeE D μ τ hs hsq (by norm_num) (by norm_num))
      hns D μ τ hs
  -- Case C
  rcases Erdos634.Draft.LemmaCFinal.lemmaC_general D hirr hB with hR | hT | hS | hTP | h32
  · exact caseR_of_odd 105 (by norm_num) D hR
  · obtain ⟨α, a, b, c, hα, hd, i, j, hij, hi, hj⟩ := hT
    exact Erdos634.Draft.CompositeFinal10.caseG_of_squarefree 105 hsq D α a b c hα hd i j hij hi hj
  · obtain ⟨α, a, b, c, hα, hd⟩ := hS
    exact gapE60_105 D α a b c hα hd hE
  · obtain ⟨α, a, b, c, hα, hd, hsh⟩ := hTP
    rcases hsh with he | hi | hf | hr
    · exact gapE120_of_chk hN0 (by decide +kernel) D α a b c hα hd he
    · exact isoClosed_of_chk hN0 (by decide +kernel) D α a b c hα hd hi
    · exact f1_not_equilateral D hα hf hE
    · exact gapR8_of_chk_z (by decide +kernel) (by decide +kernel) (by decide +kernel) D α a b c hα hd hr
  · obtain ⟨α, β, a, b, c, hα, hrel, hd, hsh⟩ := h32
    obtain ⟨σ, m0, o0, m1, o1, m2, o2⟩ := id hd
    have s01 : σ 0 ≠ σ 1 := σ.injective.ne (by decide)
    have s20 : σ 2 ≠ σ 0 := σ.injective.ne (by decide)
    have s21 : σ 2 ≠ σ 1 := σ.injective.ne (by decide)
    rcases hsh with ⟨τ, t0, t1, t2⟩ | ⟨τ, t0, t1, t2⟩ | ⟨τ, t0, t1, t2⟩ | ⟨τ, t0, t1, t2⟩ |
        ⟨τ, t0, t1, t2⟩
    · obtain ⟨r, hr, hb⟩ := Row12.rational_any_label D hα hrel hd
        (τ.injective.ne (by decide : (0 : Fin 3) ≠ 1)) t0 t1
      exact s1Closed_of_sqfree 105 hsq hN0 D α β a b c r hα hrel hd hr hb ⟨τ, t0, t1, t2⟩
    · obtain ⟨r, hr, hb⟩ := Row13.rational_any_label D hα hrel hd
        (τ.injective.ne (by decide : (0 : Fin 3) ≠ 1)) t0 t1
      exact not_baseBetaTiled (Erdos634.Draft.RASquarefree.raStatement_sqfree 105 D hsq α β a b c r hα hrel hd hr hb
        ⟨τ, t0, t1, t2⟩)
    · obtain ⟨r, hr⟩ := Row14.rational_any_label D α β hα hrel s01 s20 s21 m0 m1
        (τ.injective.ne (by decide : (0 : Fin 3) ≠ 1)) t0 t1
      rw [o0, o2] at hr
      exact not_baseBetaTiled (Erdos634.Draft.RWSquarefree.rwStatement_sqfree 105 D hsq α β a b c r hα hrel hd hr
        (Rows11_13AnyLabel.b_of_rational hrel hd hr) ⟨τ, t0, t1, t2⟩)
    · obtain ⟨r, hr, -⟩ := Row15.rational_any_label D α β hα hrel s01 s20 s21 m0 m1
        (τ.injective.ne (by decide : (0 : Fin 3) ≠ 1)) t0 t1
      rw [o0, o2] at hr
      exact s2Closed_of_arith 105 (s2Arith_of_chk hN0 (by decide +kernel)) D α β a b c r hα hrel hd hr
        (Rows11_13AnyLabel.b_of_rational hrel hd hr) ⟨τ, t0, t1, t2⟩
    · exact s3Closed_of_isoQRef 105 (isoQRef_of_chk hN0 (by decide +kernel)) D α β a b c hα hrel hd (τ 0) (τ 1)
        (τ.injective.ne (by decide : (0 : Fin 3) ≠ 1)) t0 t1

end Erdos634.Draft.Eq105

#print axioms Erdos634.Draft.Eq105.gapE60_105
#print axioms Erdos634.Draft.Eq105.eq105
