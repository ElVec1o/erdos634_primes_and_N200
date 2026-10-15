-- No sorry, no native_decide, no axioms.
-- Negative controls: for each leaf of `CompositeFinal3.chain_gen3` the leaf statement is false at the N
-- of a certified dissection (so its structural premises are jointly satisfiable), and the leaf's
-- decidable arithmetic check (`Chk`) is false there. Where the leaf is itself an arithmetic hypothesis
-- (IsoH9b) it is the hypothesis that fails.
import Erdos634.Draft.G3CSixtyControl
import Erdos634.Draft.G3CF1nControl
import Erdos634.Draft.G3CF1pControl
import Erdos634.Draft.G3CIsoControl
import Erdos634.Draft.G3CR88Control
import Erdos634.Draft.G3CEqui135Control
import Erdos634.Draft.G3CS3Control
import Erdos634.Draft.CaseALemmaVWitness
import Erdos634.Draft.LemmaSAll
import Erdos634.Draft.FluxCSimilarWitness
import Erdos634.Draft.H1Witnesses
import Erdos634.Draft.Row15JointWitness
import Erdos634.Draft.CompositeS2Arith
import Erdos634.Draft.AllN2Cond
import Erdos634.Draft.ThmIsoH9b

open scoped Classical

namespace Erdos634.Draft.G3CLeafFalse

open Erdos634.Geometry Erdos634.Draft.TheoremPConditional Erdos634.Draft.Chain15 Erdos634.Draft.ChainComposite
open Erdos634.Draft.CompositeGen2 Erdos634.Draft.AllNExclusion

/-! ### GapAcomp, N = 2 -/
theorem not_gapAcomp_2 : ¬ GapAcomp 2 := by
  intro h
  refine h Erdos634.LemmaSAll.lemmaS Erdos634.Draft.CaseALemmaHPiFour.dissection (fun k => ?_)
  refine ⟨((![1, 2, 1] k : ℕ) : ℚ) / ((4 : ℕ) : ℚ), ?_⟩
  rw [Erdos634.Draft.CaseALemmaVWitness.model_angles k]
  push_cast; ring

/-! ### CaseB, N = 4 -/
theorem not_caseBClosed_4 : ¬ CaseBClosed 4 := by
  intro h
  exact h Erdos634.Draft.FluxPaperWitness.D357 2 1
    (fun k => by simpa using Erdos634.Draft.FluxCSimilarWitness.D357_sim k)

/-! ### CaseR, N = 2 ; H1Right N = 2 (consistency instance: conclusion true) -/
theorem not_caseRClosed_2 : ¬ CaseRClosed 2 := fun h => h _ Erdos634.Draft.H1Witnesses.rightCase_witness

theorem h1Right_2_nonvacuous :
    ∃ D : CongruentDissection 2, RightCase D ∧ ∃ x y : ℕ, 2 = 2 * (x ^ 2 + y ^ 2) :=
  ⟨_, Erdos634.Draft.H1Witnesses.rightCase_witness, 1, 0, by norm_num⟩

/-! ### GapE60, N = 1440 -/
open Erdos634.Draft.G3CSixtyControl in
theorem not_gapE60_1440 : ¬ GapE60 1440 := by
  intro g
  have h := Erdos634.Draft.G3CEqui60n1440.cert_len
  rw [← h] at g
  exact g D α _ _ _ α_irr data equilateral

theorem not_pairs60Chk'_1440 : ¬ Erdos634.Draft.AllN2.Pairs60Chk' 1440 := fun h =>
  not_gapE60_1440 (Erdos634.Draft.AllN2.gapE60_of_chk' (by norm_num) h)

theorem not_pairs60Chk'_1440_direct : ¬ Erdos634.Draft.AllN2.Pairs60Chk' 1440 := by decide +kernel

/-! ### GapF1, N = 3240 (F1) and N = 1944 (F1') -/
open Erdos634.Draft.G3CF1nControl in
theorem not_gapF1_3240 : ¬ GapF1 3240 := by
  intro g
  have h := Erdos634.Draft.G3CF1n3240.cert_len
  rw [← h] at g
  exact g D α _ _ _ α_irr data f1_shape

theorem not_f1Chk_3240 : ¬ F1Chk 3240 := fun h => not_gapF1_3240 (gapF1_of_chk (by norm_num) h)
theorem not_f1Chk_3240_direct : ¬ F1Chk 3240 := by decide +kernel

open Erdos634.Draft.G3CF1pControl in
theorem not_gapF1_1944 : ¬ GapF1 1944 := by
  intro g
  have h := Erdos634.Draft.G3CF1p1944.cert_len
  rw [← h] at g
  exact g D α _ _ _ α_irr data f1_shape

theorem not_f1Chk_1944 : ¬ F1Chk 1944 := fun h => not_gapF1_1944 (gapF1_of_chk (by norm_num) h)
theorem not_f1Chk_1944_direct : ¬ F1Chk 1944 := by decide +kernel

/-! ### GapR8, N = 88 (F4) -/
open Erdos634.Draft.G3CR88Control in
theorem not_gapR8_88 : ¬ GapR8 88 := by
  intro g
  have h : R88Tiling.tiles.length = 88 := by decide
  rw [← h] at g
  exact g D α _ _ _ α_irr data88 f4_shape

theorem not_noF4zChk_88 : ¬ NoF4zChk 88 := by decide +kernel

/-- `GapR8`'s arithmetic hypotheses cannot all hold at 88. -/
theorem not_all_r8Chk_88 : ¬ (NoF2Chk 88 ∧ NoF3Chk 88 ∧ NoF4zChk 88) := fun ⟨a, b, c⟩ =>
  not_gapR8_88 (gapR8_of_chk a b c)

/-! ### IsoH9b, N = 2673: structural premises hold on the real dissection AND the arithmetic hypothesis fails -/
theorem not_isoH9b_2673 : ¬ IsoH9b 2673 := by
  intro h
  exact h 5 3 7 27 (-9) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    ⟨4, -1, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem not_isoH9bChk_2673 : ¬ IsoH9bChk 2673 := fun h => not_isoH9b_2673 (isoH9b_of_chk (by norm_num) h)
theorem not_isoH9bChk_2673_direct : ¬ IsoH9bChk 2673 := by decide +kernel

open Erdos634.Draft.G3CIsoControl in
theorem iso_leaf_witness_2673 :
    (∃ (N : ℕ) (D : CongruentDissection N) (α a b c : ℝ), IrrPi α ∧ D.model.TwoPiThreeData α a b c ∧ IsoTP D α ∧
      N = 2673) ∧ ¬ IsoH9b 2673 := by
  refine ⟨⟨_, D, α, _, _, _, α_irr, data, iso_shape, ?_⟩, not_isoH9b_2673⟩
  exact Erdos634.Draft.G3CIso2673.cert_len

/-! ### S2Closed, N = 77 -/
theorem not_s2Closed_77 : ¬ S2Closed 77 := by
  intro g
  have h : Tiling77.tiles.length = 77 := by decide
  rw [← h] at g
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := rMinus4_premises_77
  exact g D77 _ _ 32 48 64 (1 / 2) h1 h2 h3 h4 h5 h6

theorem not_s2Chk_77 : ¬ S2Chk 77 := fun h =>
  not_s2Closed_77 (Erdos634.Draft.CompositeS2Arith.s2Closed_of_arith 77
    (s2Arith_of_chk (by norm_num) h))

end Erdos634.Draft.G3CLeafFalse

#print axioms Erdos634.Draft.G3CLeafFalse.not_gapAcomp_2
#print axioms Erdos634.Draft.G3CLeafFalse.not_caseBClosed_4
#print axioms Erdos634.Draft.G3CLeafFalse.not_caseRClosed_2
#print axioms Erdos634.Draft.G3CLeafFalse.h1Right_2_nonvacuous
#print axioms Erdos634.Draft.G3CLeafFalse.not_gapE60_1440
#print axioms Erdos634.Draft.G3CLeafFalse.not_pairs60Chk'_1440
#print axioms Erdos634.Draft.G3CLeafFalse.not_pairs60Chk'_1440_direct
#print axioms Erdos634.Draft.G3CLeafFalse.not_gapF1_3240
#print axioms Erdos634.Draft.G3CLeafFalse.not_f1Chk_3240
#print axioms Erdos634.Draft.G3CLeafFalse.not_f1Chk_3240_direct
#print axioms Erdos634.Draft.G3CLeafFalse.not_gapF1_1944
#print axioms Erdos634.Draft.G3CLeafFalse.not_f1Chk_1944
#print axioms Erdos634.Draft.G3CLeafFalse.not_f1Chk_1944_direct
#print axioms Erdos634.Draft.G3CLeafFalse.not_gapR8_88
#print axioms Erdos634.Draft.G3CLeafFalse.not_noF4zChk_88
#print axioms Erdos634.Draft.G3CLeafFalse.not_all_r8Chk_88
#print axioms Erdos634.Draft.G3CLeafFalse.not_isoH9b_2673
#print axioms Erdos634.Draft.G3CLeafFalse.not_isoH9bChk_2673
#print axioms Erdos634.Draft.G3CLeafFalse.not_isoH9bChk_2673_direct
#print axioms Erdos634.Draft.G3CLeafFalse.iso_leaf_witness_2673
#print axioms Erdos634.Draft.G3CLeafFalse.not_s2Closed_77
#print axioms Erdos634.Draft.G3CLeafFalse.not_s2Chk_77
