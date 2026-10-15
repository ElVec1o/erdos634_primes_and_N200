/-
Draft/GPairs132.lean -- the `γ = 2α` leaf (`CaseGClosed N`) for `N = 132` and `N = 135`, pair by pair.

`Row4.P5` gives the pairs `(M, M')`, `M M' = N`, `M ≡ M' ≡ N (2)`, `3M < M'`:
* `N = 132`: `(2, 66)` (Lemma G*, `GPairCert.gPair_of_leafG`) and `(6, 22)`: tile `(16, 33, 28)`, target legs `264`, base
  `462`, certificate `Refl.MG132.not_dissection` (30,307 nodes);
* `N = 135`: `(1, 135)` and `(5, 27)` (coprimality, `GPairArith.gPair_of_coprime`) and `(3, 45)`: tile `(49, 15, 56)`,
  target legs `315`, base `360`, certificate `Refl.MG135.not_dissection` (33,395 nodes).

Composite-N leaf work; not prime-case work.  `N = 132` and `N = 135` stay undecided (other leaves are open).
No sorry, no native_decide.
-/
import Erdos634.Draft.GPairArith
import Erdos634.Refl.MG132Sound
import Erdos634.Refl.MG135Sound

open scoped Classical
set_option maxRecDepth 8000
set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000

namespace Erdos634.Draft.GPairs132

open Erdos634.Geometry Erdos634.Draft.ChainComposite Erdos634.Draft.GPairCert Erdos634.Draft.GPairArith
open Erdos634.Draft.FDBBaseBetaE1 Erdos634.CertNode Erdos634.CertCoord

/-! ## `N = 132` -/

theorem TGT_132 : dist (Refl.MG132.TGT.pts 0) (Refl.MG132.TGT.pts 1) = 462 ∧
    dist (Refl.MG132.TGT.pts 1) (Refl.MG132.TGT.pts 2) = 264 ∧
    dist (Refl.MG132.TGT.pts 0) (Refl.MG132.TGT.pts 2) = 264 :=
  model_sides_rp Refl.MG132.hDn Refl.MG132.TGT_pos (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

/-- the pair `(M, M') = (6, 22)`: tile `(16, 33, 28)`, target legs `264`, base `462` -/
theorem gpair_6_22 : GPair 132 6 22 := by
  obtain ⟨g1, g2, g3⟩ := TGT_132
  obtain ⟨k1, k2, k3⟩ := Refl.MG132.MODEL_sides
  exact gPair_of_cert 132 6 22 (by norm_num) 264 462 16 33 28 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) Refl.MG132.TGT Refl.MG132.MODEL
    (fun T h => congruent_of_hasSides' h g1 g2 g3)
    (fun T h => congruent_of_hasSides' (hasSides_rot h) k1 k2 k3)
    (fun D' hT hM => Refl.MG132.not_dissection D' hT hM)

/-- **`CaseGClosed 132`** (`γ = 2α`): the pairs `(2, 66)` (Lemma G*) and `(6, 22)` (certificate). -/
theorem caseG132 : CaseGClosed 132 := by
  refine caseG_of_pairs 132 [(2, 66), (6, 22)] ?_ ?_
  · intro M M' hM hM' hN h1 h2 h3
    push_cast at hN h1 h2
    have hM7 : M ≤ 6 := by nlinarith
    have key : (M = 2 ∧ M' = 66) ∨ (M = 6 ∧ M' = 22) := by
      interval_cases M <;> omega
    rcases key with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · have h := gPair_of_leafG 132 16 (by norm_num)
      norm_num at h
      exact h
    · exact gpair_6_22

/-! ## `N = 135` -/

theorem TGT_135 : dist (Refl.MG135.TGT.pts 0) (Refl.MG135.TGT.pts 1) = 360 ∧
    dist (Refl.MG135.TGT.pts 1) (Refl.MG135.TGT.pts 2) = 315 ∧
    dist (Refl.MG135.TGT.pts 0) (Refl.MG135.TGT.pts 2) = 315 :=
  model_sides_rp Refl.MG135.hDn Refl.MG135.TGT_pos (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

/-- the pair `(M, M') = (3, 45)`: tile `(49, 15, 56)`, target legs `315`, base `360` -/
theorem gpair_3_45 : GPair 135 3 45 := by
  obtain ⟨g1, g2, g3⟩ := TGT_135
  obtain ⟨k1, k2, k3⟩ := Refl.MG135.MODEL_sides
  exact gPair_of_cert 135 3 45 (by norm_num) 315 360 49 15 56 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) Refl.MG135.TGT Refl.MG135.MODEL
    (fun T h => congruent_of_hasSides' h g1 g2 g3)
    (fun T h => congruent_of_hasSides' (hasSides_rot h) k1 k2 k3)
    (fun D' hT hM => Refl.MG135.not_dissection D' hT hM)

/-- **`CaseGClosed 135`** (`γ = 2α`): `(1, 135)` and `(5, 27)` (coprimality), `(3, 45)` (certificate). -/
theorem caseG135 : CaseGClosed 135 := by
  refine caseG_of_pairs 135 [(1, 135), (3, 45), (5, 27)] ?_ ?_
  · intro M M' hM hM' hN h1 h2 h3
    push_cast at hN h1 h2
    have hM7 : M ≤ 6 := by nlinarith
    have key : (M = 1 ∧ M' = 135) ∨ (M = 3 ∧ M' = 45) ∨ (M = 5 ∧ M' = 27) := by
      interval_cases M <;> omega
    rcases key with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl
    · exact_mod_cast gPair_of_coprime 135 1 135 (by norm_num) (by norm_num) (by decide)
    · exact gpair_3_45
    · exact_mod_cast gPair_of_coprime 135 5 27 (by norm_num) (by norm_num) (by decide)

end Erdos634.Draft.GPairs132

#print axioms Erdos634.Draft.GPairs132.caseG132
#print axioms Erdos634.Draft.GPairs132.caseG135
