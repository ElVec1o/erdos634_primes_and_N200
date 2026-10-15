/-
Draft/N171.lean -- `N = 171` is NOT a tile count.

`171 = 9 · 19`.  Every leaf of the non-squarefree chain holds by kernel-checked arithmetic except three:
* the `π/3` equilateral leaf: `E60Apps.gapE60_171` (the only pair left by the arithmetic, `(57, 9)`, has the non-square
  discriminant `1620`, so it is excluded by `E60Irr.e60Pair_of_not_isSquare`: the relation `j a = p b + q c` of
  `E60Graph.sixty_has_a_relation`; no certificate);
* the S5 leaf: the single instance `(t, e, f) = (3, 9, 10)`, tile `(90, 19, 100)` in `(570, 570, 513)`, certificate
  `Refl.MS171.not_dissection` (121,680 nodes);
* the `γ = 2α` leaf: the pairs of `Row4.P5` are `(M, M') = (1, 171)`, dead by coprimality (`GPairArith.gPair_of_coprime`),
  and `(3, 57)`, tile `(81, 19, 90)` in `(513, 513, 570)`, certificate `Refl.MG171.not_dissection` (26,496 nodes).

Composite-N result.  No sorry, no native_decide.
-/
import Erdos634.Draft.E60Apps
import Erdos634.Draft.E60Reduce
import Erdos634.Draft.GPairArith
import Erdos634.Draft.RAInst
import Erdos634.Refl.MS171Sound
import Erdos634.Refl.MG171Sound

open scoped Classical
set_option maxRecDepth 8000
set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000

namespace Erdos634.Draft.N171

open Erdos634.Geometry Erdos634.Draft.AllNExclusion Erdos634.Draft.AllN2 Erdos634.Draft.NSQMain Erdos634.Draft.NSQM
open Erdos634.Draft.NSQChk Erdos634.Draft.NSQLegs Erdos634.Draft.NSQS1 Erdos634.Draft.NSQRW Erdos634.Draft.NSQRA
open Erdos634.Draft.R8ZF Erdos634.Draft.E60Reduce Erdos634.Draft.Chain15 Erdos634.Draft.ChainComposite
open Erdos634.Draft.GPairCert Erdos634.Draft.GPairArith Erdos634.Draft.FDBBaseBetaE1
open Erdos634.CertNode Erdos634.CertCoord

/-! ## S5 -/

theorem TGT_S : dist (Refl.MS171.TGT.pts 0) (Refl.MS171.TGT.pts 1) = 513 ∧
    dist (Refl.MS171.TGT.pts 1) (Refl.MS171.TGT.pts 2) = 570 ∧ dist (Refl.MS171.TGT.pts 0) (Refl.MS171.TGT.pts 2) = 570 :=
  model_sides_rp Refl.MS171.hDn Refl.MS171.TGT_pos (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

/-- S5 `(t,e,f) = (3,9,10)`: tile `(90,19,100)`, target `(570,570,513)`. -/
theorem s5inst_3_9_10 : S5Inst 3 9 10 :=
  s5inst_of_cert 3 9 10 Refl.MS171.TGT Refl.MS171.MODEL
    ⟨by rw [TGT_S.1]; norm_num, by rw [TGT_S.2.1]; norm_num, by rw [TGT_S.2.2]; norm_num⟩
    ⟨by rw [Refl.MS171.MODEL_sides.1]; norm_num, by rw [Refl.MS171.MODEL_sides.2.1]; norm_num,
      by rw [Refl.MS171.MODEL_sides.2.2]; norm_num⟩
    (fun D hT hM => Refl.MS171.not_dissection D hT hM)

/-- **`RAStatementNsq 171`** (S5): the scaled instance `(3,9,10)`. -/
theorem ra171 : RAStatementNsq 171 := by
  refine raStatement_of_inst 171 ?_
  intro t e f ht he hef hcop hN
  push_cast at hN
  have hd : 2 * f - 1 ≤ f ^ 2 - e ^ 2 := by nlinarith
  have ht4 : 4 ≤ t ^ 2 := by nlinarith
  have hf : f ≤ 21 := by nlinarith
  have hf2 : 2 ≤ f := by omega
  have ht5 : t ≤ 7 := by
    by_contra h; push_neg at h
    have : 64 ≤ t ^ 2 := by nlinarith
    nlinarith
  interval_cases t <;> interval_cases f <;> interval_cases e <;>
    first | (norm_num at hN; done) | exact @s5inst_3_9_10

/-! ## `γ = 2α` -/

theorem TGT_G : dist (Refl.MG171.TGT.pts 0) (Refl.MG171.TGT.pts 1) = 570 ∧
    dist (Refl.MG171.TGT.pts 1) (Refl.MG171.TGT.pts 2) = 513 ∧ dist (Refl.MG171.TGT.pts 0) (Refl.MG171.TGT.pts 2) = 513 :=
  model_sides_rp Refl.MG171.hDn Refl.MG171.TGT_pos (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

/-- the pair `(M, M') = (3, 57)`: tile `(81, 19, 90)`, target legs `513`, base `570` -/
theorem gpair_3_57 : GPair 171 3 57 := by
  obtain ⟨g1, g2, g3⟩ := TGT_G
  obtain ⟨k1, k2, k3⟩ := Refl.MG171.MODEL_sides
  exact gPair_of_cert 171 3 57 (by norm_num) 513 570 81 19 90 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) Refl.MG171.TGT Refl.MG171.MODEL
    (fun T h => congruent_of_hasSides' h g1 g2 g3)
    (fun T h => congruent_of_hasSides' (hasSides_rot h) k1 k2 k3)
    (fun D' hT hM => Refl.MG171.not_dissection D' hT hM)

/-- **`CaseGClosed 171`** (`γ = 2α`): the pairs `(1, 171)` (coprimality) and `(3, 57)` (certificate). -/
theorem caseG171 : CaseGClosed 171 := by
  refine caseG_of_pairs 171 [(1, 171), (3, 57)] ?_ ?_
  · intro M M' hM hM' hN h1 h2 h3
    push_cast at hN h1 h2
    have hM7 : M ≤ 7 := by nlinarith
    have key : (M = 1 ∧ M' = 171) ∨ (M = 3 ∧ M' = 57) := by
      interval_cases M <;> omega
    rcases key with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact_mod_cast gPair_of_coprime 171 1 171 (by norm_num) (by norm_num) (by decide)
    · exact gpair_3_57

/-- **`171` is not a tile count** (no `CongruentDissection 171` exists). -/
theorem not_tile_171 (D : CongruentDissection 171) : False :=
  not_tile_of_e60_s5_g 171 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ra171 caseG171
    Erdos634.Draft.E60Apps.gapE60_171 D

end Erdos634.Draft.N171

#print axioms Erdos634.Draft.N171.not_tile_171
