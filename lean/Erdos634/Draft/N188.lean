/-
Draft/N188.lean -- `N = 188` is NOT a tile count.

`188 = 4 · 47`.  Failing search-type leaves: S1, S4, S5 and `γ = 2α`.
* S1 `(t,p,q) = (2,1,4)`: tile (4,15,16) in (128,128,94) -- certificate `Refl.MS1N188.not_dissection` (56,629 nodes).
* S4 `(S',e,f) = (2,5,6)`: tile (30,11,36) in (470,132,432) -- certificate `Refl.MC188.not_dissection` (3,514 nodes).
* S5: the only instance is `(t,e,f) = (2,23,24)`, of the family `(2,k,k+1)`; its base has no word with two `c`-edges
  (`NSQM.s5word2_k`), so it needs NO certificate (`NSQM.raStatement_of_inst_trap2`).
* `γ = 2α`: `M = 2`, `k = 23`, `GLK.caseG_of_leafOnly`.

Composite-N result.  No sorry, no native_decide.
-/
import Erdos634.Draft.N92
import Erdos634.Draft.RATrap2
import Erdos634.Refl.MS1N188Sound
import Erdos634.Refl.MC188Sound
import Erdos634.Draft.HasSidesPerm

open scoped Classical
set_option maxRecDepth 8000
set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000

namespace Erdos634.Draft.N188

open Erdos634.Geometry Erdos634.Draft.TheoremPConditional Erdos634.Draft.Chain15 Erdos634.Draft.ChainComposite
open Erdos634.Draft.CompositeGen2 Erdos634.Draft.CompositeArith Erdos634.Draft.CompositeS2Arith
open Erdos634.Draft.CompositeS1Arith Erdos634.Draft.CompositeIsoB Erdos634.Draft.CompositeFinal2
open Erdos634.Draft.CompositeFinal3 Erdos634.Draft.AllNExclusion Erdos634.Draft.AllN2
open Erdos634.Draft.NSQRA Erdos634.Draft.NSQRW Erdos634.Draft.NSQS1 Erdos634.Draft.NSQChk Erdos634.Draft.NSQLegs
open Erdos634.Draft.NSQMain Erdos634.Draft.NSQM Erdos634.CertNode Erdos634.CertCoord
open Erdos634.Draft.N566076 Erdos634.Draft.N92 Erdos634.Draft.CompositeFinal4 Erdos634.Draft.FDBBaseBetaE1

theorem TGT_S1 : dist (Refl.MS1N188.TGT.pts 0) (Refl.MS1N188.TGT.pts 1) = 94 ∧
    dist (Refl.MS1N188.TGT.pts 1) (Refl.MS1N188.TGT.pts 2) = 128 ∧
    dist (Refl.MS1N188.TGT.pts 0) (Refl.MS1N188.TGT.pts 2) = 128 :=
  model_sides_rp Refl.MS1N188.hDn Refl.MS1N188.TGT_pos (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

/-- S1 `(t,p,q) = (2,1,4)`: tile `(4,15,16)`, target legs `128`, base `94`. -/
theorem s1inst_2_1_4 : S1Inst 2 1 4 := by
  intro N D h0 h1 h2 ⟨σ, m0, m1, m2⟩
  obtain ⟨g1, g2, g3⟩ := TGT_S1
  obtain ⟨k1, k2, k3⟩ := Refl.MS1N188.MODEL_sides
  have hT : HasSides D.target 128 128 94 :=
    hasSides_of_oppLen (by rw [h0]; norm_num) (by rw [h1]; norm_num) (by rw [h2]; norm_num)
  have hM : HasSides D.model 4 15 16 :=
    hasSides_of_sigma σ (by rw [m0]; norm_num) (by rw [m1]; norm_num) (by rw [m2]; norm_num)
  exact Refl.MS1N188.not_dissection D (congruent_of_hasSides' hT g1 g2 g3)
    (congruent_of_hasSides' (hasSides_rot hM) k1 k2 k3)

/-- **`S1Closed 188`**: the scaled instance `(2,1,4)`. -/
theorem s1Closed : S1Closed 188 := by
  refine s1Closed_of_inst 188 ?_
  intro t p q ht hp hpq hcop hN
  push_cast at hN
  have hd : 2 * q ^ 2 + 2 * q - 1 ≤ 3 * q ^ 2 - p ^ 2 := by nlinarith
  have ht4 : 4 ≤ t ^ 2 := by nlinarith
  have hq2 : 2 ≤ q := by omega
  have hq : q ≤ 4 := by nlinarith
  have ht5 : t ≤ 4 := by
    by_contra h; push_neg at h
    have : 25 ≤ t ^ 2 := by nlinarith
    nlinarith
  interval_cases t <;> interval_cases q <;> interval_cases p <;>
    first | (norm_num at hN; done) | exact @s1inst_2_1_4

theorem TGT_C : dist (Refl.MC188.TGT.pts 0) (Refl.MC188.TGT.pts 1) = 132 ∧
    dist (Refl.MC188.TGT.pts 1) (Refl.MC188.TGT.pts 2) = 470 ∧ dist (Refl.MC188.TGT.pts 0) (Refl.MC188.TGT.pts 2) = 432 :=
  model_sides_rp Refl.MC188.hDn Refl.MC188.TGT_pos (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

/-- S4 `(S',e,f) = (2,5,6)`: tile `(30,11,36)`, target `(470,132,432)`. -/
theorem s4inst_2_5_6 : S4Inst 2 5 6 := by
  intro N D h0 h1 h2 ⟨σ, m0, m1, m2⟩
  obtain ⟨g1, g2, g3⟩ := TGT_C
  obtain ⟨k1, k2, k3⟩ := Refl.MC188.MODEL_sides
  have hT : HasSides D.target 470 132 432 :=
    hasSides_of_oppLen (by rw [h0]; norm_num) (by rw [h1]; norm_num) (by rw [h2]; norm_num)
  have hM : HasSides D.model 30 11 36 :=
    hasSides_of_sigma σ (by rw [m0]; norm_num) (by rw [m1]; norm_num) (by rw [m2]; norm_num)
  exact Refl.MC188.not_dissection D
    (congruent_of_hasSides' (hasSides_rot (hasSides_swap hT)) g1 g2 g3)
    (congruent_of_hasSides' (hasSides_rot hM) k1 k2 k3)

/-- **`RWStatementNsq 188`** (S4): the scaled instance `(2,5,6)`. -/
theorem rw188 : RWStatementNsq 188 := by
  refine rwStatement_of_inst 188 ?_
  intro S' e f hS he hef hcop hN
  push_cast at hN
  have hd : f ^ 2 + 2 * f - 1 ≤ 2 * f ^ 2 - e ^ 2 := by nlinarith
  have hS4 : 4 ≤ S' ^ 2 := by nlinarith
  have hf2 : 2 ≤ f := by omega
  have hf : f ≤ 6 := by nlinarith
  have hS5 : S' ≤ 5 := by
    by_contra h; push_neg at h
    have : 36 ≤ S' ^ 2 := by nlinarith
    nlinarith
  interval_cases S' <;> interval_cases f <;> interval_cases e <;>
    first | (norm_num at hN; done) | exact @s4inst_2_5_6

/-- **`RAStatementNsq 188`** (S5): the only instance is `(2,23,24)`, dead by the two-`c`-edges filter. -/
theorem ra : RAStatementNsq 188 := by
  refine raStatement_of_inst_trap2 188 ?_
  intro t e f ht he hef hcop hN hwb _
  push_cast at hN
  have hd : 2 * f - 1 ≤ f ^ 2 - e ^ 2 := by nlinarith
  have ht4 : 4 ≤ t ^ 2 := by nlinarith
  have hf : f ≤ 24 := by nlinarith
  have ht5 : t ≤ 7 := by
    by_contra h; push_neg at h
    have : 64 ≤ t ^ 2 := by nlinarith
    nlinarith
  have hf2 : 2 ≤ f := by omega
  have hk : ¬ S5Word2 2 23 24 := s5word2_k (k := 23) (by norm_num)
  interval_cases t <;> interval_cases f <;> interval_cases e <;>
    first | (norm_num at hN; done) | (exfalso; exact hk hwb)

theorem arith : ∀ M M' : ℤ, 0 < M → 0 < M' → ((188 : ℕ) : ℤ) = M * M' → (2 : ℤ) ∣ M - ((188 : ℕ) : ℤ) →
    (2 : ℤ) ∣ M' - ((188 : ℕ) : ℤ) → 3 * M < M' → M = 2 ∧ M' = 2 * (2 * ((23 : ℕ) : ℤ) + 1) := by
  intro M M' hM hM' hN h1 h2 h3
  push_cast at *
  have : M ≤ 7 := by nlinarith
  interval_cases M <;> omega

/-- `CaseGClosed 188` (`γ = 2α`). -/
theorem caseG : CaseGClosed 188 := Erdos634.GLK.caseG_of_leafOnly 188 23 (by norm_num) arith

/-- **`188` is not a tile count** (no `CongruentDissection 188` exists). -/
theorem not_tile_188 (D : CongruentDissection 188) : False :=
  not_tile_of_leaves_s1 188 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (gapE60_of_chk' (by norm_num) (by decide +kernel)) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    s1Closed rw188 ra caseG (gapE120_of_chk (by norm_num) (by decide +kernel)) D

end Erdos634.Draft.N188

#print axioms Erdos634.Draft.N188.not_tile_188
