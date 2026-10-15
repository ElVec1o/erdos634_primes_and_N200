/-
Draft/GPairs156.lean -- the `γ = 2α` leaf (`CaseGClosed 156`), pair by pair.

`Row4.P5` gives the pairs `(M, M')`, `M M' = 156`, `M ≡ M' ≡ 156 (2)`, `3M < M'`:
* `(2, 78)`: Lemma G* (`GPairCert.gPair_of_leafG`, `156 = 4 (2·19 + 1)`);
* `(6, 26)`: tile `(25, 39, 40)`, target legs `390`, base `624`, certificate `Refl.MG156.not_dissection`
  (87,352 nodes; the first certificate with rational coordinates, radicand `1`: the tile has area `468` and the
  target has height `234`).

Composite-N leaf work; not prime-case work.  `N = 156` stays undecided (its S1 instance, the member `(3, 4)` at
scale `m = 2`, is open).  No sorry, no native_decide.
-/
import Erdos634.Draft.GPairArith
import Erdos634.Refl.MG156Sound

open scoped Classical
set_option maxRecDepth 8000
set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000

namespace Erdos634.Draft.GPairs156

open Erdos634.Geometry Erdos634.Draft.ChainComposite Erdos634.Draft.GPairCert Erdos634.Draft.GPairArith
open Erdos634.Draft.FDBBaseBetaE1 Erdos634.CertNode Erdos634.CertCoord

theorem TGT_156 : dist (Refl.MG156.TGT.pts 0) (Refl.MG156.TGT.pts 1) = 624 ∧
    dist (Refl.MG156.TGT.pts 1) (Refl.MG156.TGT.pts 2) = 390 ∧
    dist (Refl.MG156.TGT.pts 0) (Refl.MG156.TGT.pts 2) = 390 :=
  model_sides_rp Refl.MG156.hDn Refl.MG156.TGT_pos (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

/-- the pair `(M, M') = (6, 26)`: tile `(25, 39, 40)`, target legs `390`, base `624` -/
theorem gpair_6_26 : GPair 156 6 26 := by
  obtain ⟨g1, g2, g3⟩ := TGT_156
  obtain ⟨k1, k2, k3⟩ := Refl.MG156.MODEL_sides
  exact gPair_of_cert 156 6 26 (by norm_num) 390 624 25 39 40 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) Refl.MG156.TGT Refl.MG156.MODEL
    (fun T h => congruent_of_hasSides' h g1 g2 g3)
    (fun T h => congruent_of_hasSides' (hasSides_rot h) k1 k2 k3)
    (fun D' hT hM => Refl.MG156.not_dissection D' hT hM)

/-- **`CaseGClosed 156`** (`γ = 2α`): the pairs `(2, 78)` (Lemma G*) and `(6, 26)` (certificate). -/
theorem caseG156 : CaseGClosed 156 := by
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
    · have h := gPair_of_leafG 156 19 (by norm_num)
      norm_num at h
      exact h
    · exact gpair_6_26

end Erdos634.Draft.GPairs156

#print axioms Erdos634.Draft.GPairs156.caseG156
